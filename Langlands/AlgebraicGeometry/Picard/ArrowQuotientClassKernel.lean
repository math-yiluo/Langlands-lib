import Langlands.AlgebraicGeometry.Picard.ArrowQuotientEndpoints

/-! # The full kernel of the actual etale Picard family map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.SmoothRelationQuotient

variable {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  {A R : Over S} (r s : R ⟶ A)
  (eA : (AlgebraicSpace.schemeYoneda S).obj A ≅ atlasArrowPresheaf f L)
  (h : IsPullback ((AlgebraicSpace.schemeYoneda S).map r)
    ((AlgebraicSpace.schemeYoneda S).map s)
    (eA.hom ≫ atlasArrowEndpoint f L) (eA.hom ≫ atlasArrowEndpoint f L))

/-- The descended endpoints have the same actual etale Picard class. -/
lemma arrowKernelQuotient_etaleFamilyMap :
    arrowKernelQuotientFst f L r s eA h ≫ etaleFamilyMap f L =
      arrowKernelQuotientSnd f L r s eA h ≫ etaleFamilyMap f L := by
  apply quotientSheaf_hom_ext ((AlgebraicSpace.schemeToSpace S).obj R)
    ((AlgebraicSpace.schemeYoneda S).map r) ((AlgebraicSpace.schemeYoneda S).map s)
    (representedKernel_isEquivalenceRelation r s _ h)
    (relativeEtaleClassSheaf f).property
  change arrowKernelQuotientMap f L r s eA h ≫
      (arrowKernelQuotientFst f L r s eA h ≫ etaleFamilyMap f L) =
    arrowKernelQuotientMap f L r s eA h ≫
      (arrowKernelQuotientSnd f L r s eA h ≫ etaleFamilyMap f L)
  simp only [← Category.assoc, arrowKernelQuotientMap_fst, arrowKernelQuotientMap_snd]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ eA.hom ≫ k) (atlasArrow_etaleFamilyMap f L)

/-- The two endpoints determine every section of the arrow-class sheaf. -/
lemma arrowKernelQuotient_jointlyInjective (T : Over S) :
    Function.Injective (fun q : (arrowKernelQuotientSheaf f L r s eA h).obj.obj (op T) ↦
      ((arrowKernelQuotientFst f L r s eA h).app (op T) q,
        (arrowKernelQuotientSnd f L r s eA h).app (op T) q)) := by
  let : Mono (arrowKernelQuotientEndpoint f L r s eA h) :=
    arrowKernelQuotientEndpoint_mono f L r s eA h
  have hinj := (mono_iff_injective
    ((arrowKernelQuotientEndpoint f L r s eA h).app (op T))).mp inferInstance
  intro q q' hqq'
  apply hinj
  apply ULift.ext
  exact Prod.ext
    (congrArg ULift.down (congrArg Prod.fst hqq'))
    (congrArg ULift.down (congrArg Prod.snd hqq'))

/-- Equality of actual etale family classes is witnessed by a section of the
canonical arrow-class sheaf on the complete test scheme. -/
lemma arrowKernelQuotient_exists_of_etaleFamilyMap_eq {T : Over S}
    (x y : ((AlgebraicSpace.schemeYoneda S).obj U).obj (op T))
    (hxy : (etaleFamilyMap f L).app (op T) x =
      (etaleFamilyMap f L).app (op T) y) :
    ∃ q : (arrowKernelQuotientSheaf f L r s eA h).obj.obj (op T),
      (arrowKernelQuotientFst f L r s eA h).app (op T) q = x ∧
        (arrowKernelQuotientSnd f L r s eA h).app (op T) q = y := by
  let J := Scheme.etaleTopology.over S
  let Q := (arrowKernelQuotientSheaf f L r s eA h).obj
  let a := arrowKernelQuotientFst f L r s eA h
  let b := arrowKernelQuotientSnd f L r s eA h
  let F := (AlgebraicSpace.schemeYoneda S).obj U
  let cx := (classFamilyMap f L).app (op T) x
  let cy := (classFamilyMap f L).app (op T) y
  have hxy' : (relativeToEtaleClassSheaf f).app (op T) cx =
      (relativeToEtaleClassSheaf f).app (op T) cy := by
    simpa only [← classFamilyMap_toEtale, NatTrans.comp_app, types_comp_apply] using hxy
  let Sv := Presheaf.equalizerSieve (F := relativeClassPresheaf f) cx cy
  have hmem : Sv ∈ J T :=
    Presheaf.equalizerSieve_mem (Scheme.etaleTopology.over S)
      (toSheafify (Scheme.etaleTopology.over S) (relativeClassPresheaf f)) cx cy hxy'
  have hlocal : ∀ ⦃V : Over S⦄ (g : V ⟶ T), Sv.arrows g →
      ∃ q : Q.obj (op V), a.app (op V) q = F.map g.op x ∧
        b.app (op V) q = F.map g.op y := by
    intro V g hg
    have hc : (classFamilyMap f L).app (op V) (F.map g.op x) =
        (classFamilyMap f L).app (op V) (F.map g.op y) := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hg
    obtain ⟨δ, hδa, hδb⟩ :=
      (classFamilyMap_eq_iff f L (g ≫ x.down) (g ≫ y.down)).mp hc
    let z := eA.inv.app (op V) δ
    refine ⟨(arrowKernelQuotientMap f L r s eA h).app (op V) z, ?_, ?_⟩
    · have ha := congrArg (fun k ↦ k.app (op V) z)
        (arrowKernelQuotientMap_fst f L r s eA h)
      have ha' : a.app (op V) ((arrowKernelQuotientMap f L r s eA h).app (op V) z) =
          (atlasArrowFst f L).app (op V) δ := by
        simpa only [NatTrans.comp_app, types_comp_apply, z,
          Iso.inv_hom_id_app_apply] using ha
      exact ha'.trans hδa
    · have hb := congrArg (fun k ↦ k.app (op V) z)
        (arrowKernelQuotientMap_snd f L r s eA h)
      have hb' : b.app (op V) ((arrowKernelQuotientMap f L r s eA h).app (op V) z) =
          (atlasArrowSnd f L).app (op V) δ := by
        simpa only [NatTrans.comp_app, types_comp_apply, z,
          Iso.inv_hom_id_app_apply] using hb
      exact hb'.trans hδb
  let fam : Presieve.FamilyOfElements Q Sv.arrows :=
    fun _ g hg ↦ (hlocal g hg).choose
  have fam_a : ∀ ⦃V : Over S⦄ (g : V ⟶ T) (hg : Sv.arrows g),
      a.app (op V) (fam g hg) = F.map g.op x :=
    fun _ g hg ↦ (hlocal g hg).choose_spec.1
  have fam_b : ∀ ⦃V : Over S⦄ (g : V ⟶ T) (hg : Sv.arrows g),
      b.app (op V) (fam g hg) = F.map g.op y :=
    fun _ g hg ↦ (hlocal g hg).choose_spec.2
  have hcompat : fam.Compatible := by
    intro V₁ V₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    apply arrowKernelQuotient_jointlyInjective f L r s eA h Z
    refine Prod.ext ?_ ?_
    · change a.app (op Z) (Q.map g₁.op (fam f₁ hf₁)) =
        a.app (op Z) (Q.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply a, NatTrans.naturality_apply a,
        fam_a f₁ hf₁, fam_a f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
    · change b.app (op Z) (Q.map g₁.op (fam f₁ hf₁)) =
        b.app (op Z) (Q.map g₂.op (fam f₂ hf₂))
      rw [NatTrans.naturality_apply b, NatTrans.naturality_apply b,
        fam_b f₁ hf₁, fam_b f₂ hf₂,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  have hQ : Presieve.IsSheaf J Q :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp
      (arrowKernelQuotientSheaf f L r s eA h).property
  have hF : Presieve.IsSheaf J F :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).mp
      ((((AlgebraicSpace.schemeSheaf S).obj U).property).of_le
        (Sites.etaleTopologyOver_le_fppfTopologyOver S))
  obtain ⟨q, hq, -⟩ := hQ Sv hmem fam hcompat
  refine ⟨q, ?_, ?_⟩
  · refine (hF Sv hmem).isSeparatedFor.ext fun V g hg ↦ ?_
    rw [← NatTrans.naturality_apply a, hq g hg, fam_a g hg]
  · refine (hF Sv hmem).isSeparatedFor.ext fun V g hg ↦ ?_
    rw [← NatTrans.naturality_apply b, hq g hg, fam_b g hg]

/-- The canonical arrow classes detect exactly equality in the actual etale
Picard family map, on all scheme sections. -/
lemma arrowKernelQuotient_relation_iff {T : Over S}
    (x y : ((AlgebraicSpace.schemeYoneda S).obj U).obj (op T)) :
    (∃ q : (arrowKernelQuotientSheaf f L r s eA h).obj.obj (op T),
      (arrowKernelQuotientFst f L r s eA h).app (op T) q = x ∧
        (arrowKernelQuotientSnd f L r s eA h).app (op T) q = y) ↔
      (etaleFamilyMap f L).app (op T) x = (etaleFamilyMap f L).app (op T) y := by
  constructor
  · rintro ⟨q, rfl, rfl⟩
    exact congrArg (fun k ↦ k.app (op T) q)
      (arrowKernelQuotient_etaleFamilyMap f L r s eA h)
  · exact arrowKernelQuotient_exists_of_etaleFamilyMap_eq f L r s eA h x y

/-- The complete arrow-class sheaf is the kernel pair of the actual etale
family-class map, including sections with only local arrow representatives. -/
lemma arrowKernelQuotient_isPullback :
    IsPullback (arrowKernelQuotientFst f L r s eA h)
      (arrowKernelQuotientSnd f L r s eA h) (etaleFamilyMap f L)
      (etaleFamilyMap f L) := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k ↦ k.app T)
    (arrowKernelQuotient_etaleFamilyMap f L r s eA h), ?_, ?_⟩
  · intro q q' hqq'
    exact arrowKernelQuotient_jointlyInjective f L r s eA h T.unop
      (Prod.ext hqq'.1 hqq'.2)
  · exact arrowKernelQuotient_exists_of_etaleFamilyMap_eq f L r s eA h

/-- Arrow classes give a monomorphic equivalence relation on the complete
section type of every test scheme. -/
lemma arrowKernelQuotient_sectionwise :
    ∀ T : Over S,
      Function.Injective (fun q : (arrowKernelQuotientSheaf f L r s eA h).obj.obj (op T) ↦
        ((arrowKernelQuotientFst f L r s eA h).app (op T) q,
          (arrowKernelQuotientSnd f L r s eA h).app (op T) q)) ∧
      Equivalence (fun x y : ((AlgebraicSpace.schemeYoneda S).obj U).obj (op T) ↦
        ∃ q : (arrowKernelQuotientSheaf f L r s eA h).obj.obj (op T),
          (arrowKernelQuotientFst f L r s eA h).app (op T) q = x ∧
            (arrowKernelQuotientSnd f L r s eA h).app (op T) q = y) := by
  intro T
  refine ⟨arrowKernelQuotient_jointlyInjective f L r s eA h T, ?_⟩
  have hiff := arrowKernelQuotient_relation_iff f L r s eA h (T := T)
  exact ⟨fun x ↦ (hiff x x).mpr rfl,
    fun {x y} hxy ↦ (hiff y x).mpr ((hiff x y).mp hxy).symm,
    fun {x y z} hxy hyz ↦
      (hiff x z).mpr (((hiff x y).mp hxy).trans ((hiff y z).mp hyz))⟩

/-- The canonical natural isomorphism with the full kernel pair of the
actual etale Picard family map. -/
def arrowKernelQuotientKernelIso :
    (arrowKernelQuotientSheaf f L r s eA h).obj ≅
      Limits.pullback (etaleFamilyMap f L) (etaleFamilyMap f L) :=
  (arrowKernelQuotient_isPullback f L r s eA h).isoPullback

/-- The kernel-pair isomorphism preserves the first actual endpoint. -/
@[simp]
lemma arrowKernelQuotientKernelIso_hom_fst :
    (arrowKernelQuotientKernelIso f L r s eA h).hom ≫ Limits.pullback.fst _ _ =
      arrowKernelQuotientFst f L r s eA h :=
  (arrowKernelQuotient_isPullback f L r s eA h).isoPullback_hom_fst

/-- The kernel-pair isomorphism preserves the second actual endpoint. -/
@[simp]
lemma arrowKernelQuotientKernelIso_hom_snd :
    (arrowKernelQuotientKernelIso f L r s eA h).hom ≫ Limits.pullback.snd _ _ =
      arrowKernelQuotientSnd f L r s eA h :=
  (arrowKernelQuotient_isPullback f L r s eA h).isoPullback_hom_snd

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
