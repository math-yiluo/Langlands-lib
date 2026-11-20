import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Langlands.AlgebraicGeometry.Picard.DualBaseChangeCoherence

/-! # Zariski locality of the conditions on ordinary polarized full-level data -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The canonical dual base change along a composite is the successive one, transported
along the comparison `baseChangeCompIso` of abelian schemes. -/
theorem dualBaseChangeMap_comp (stability : PicardZeroPullbackStatement.{u})
    (universality : PicardZeroUniversalBaseChangeStatement.{u})
    {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S') (A : AbelianScheme S)
    (hA : HasDualScheme A) (f : A.X ⟶ dualScheme A hA) :
    dualBaseChangeMap A hA universality (c ≫ b) f =
      (groupHom (baseChangeCompIso b c A).hom).hom.hom ≫
        dualBaseChangeMap ((baseChange b).obj A) (hasDualScheme_baseChange universality b A hA)
          universality c (dualBaseChangeMap A hA universality b f) ≫
        dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).hom
          (hasDualScheme_baseChange universality (c ≫ b) A hA)
          (hasDualScheme_baseChange universality c _
            (hasDualScheme_baseChange universality b A hA)) := by
  set hAb := hasDualScheme_baseChange universality b A hA
  set hAd := hasDualScheme_baseChange universality (c ≫ b) A hA
  set hAc := hasDualScheme_baseChange universality c _ hAb
  have key := dualSchemeBaseChangeIso_comp A b c stability universality hA hAb hAd hAc
  have key' : (Over.pullback c).map (dualSchemeBaseChangeIso universality b A hA hAb).hom ≫
      (dualSchemeBaseChangeIso universality c ((baseChange b).obj A) hAb hAc).hom =
      (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
        (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom ≫
          dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd := by
    rw [← key, Iso.inv_hom_id_app_assoc]
  have hd : dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd ≫
      dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).hom hAd hAc = 𝟙 _ := by
    rw [← dualSchemeMap_comp homPicardZeroPullback
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence, Iso.hom_inv_id,
      dualSchemeMap_id homPicardZeroPullback
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence]
  have hc : (groupHom (baseChangeCompIso b c A).hom).hom.hom ≫
      (Over.pullbackComp c b).inv.app A.X = 𝟙 _ := by
    simp [baseChangeCompIso, GroupScheme.baseChangeCompIso, Functor.mapGrpNatIso,
      Functor.mapGrpCompIso]
    rfl
  have hn : (Over.pullback c).map ((Over.pullback b).map f) ≫
      (Over.pullbackComp c b).inv.app (dualScheme A hA) =
      (Over.pullbackComp c b).inv.app A.X ≫ (Over.pullback (c ≫ b)).map f :=
    (Over.pullbackComp c b).inv.naturality f
  have s1 : (Over.pullback c).map (dualSchemeBaseChangeIso universality b A hA hAb).hom ≫
      (dualSchemeBaseChangeIso universality c ((baseChange b).obj A) hAb hAc).hom ≫
        dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).hom hAd hAc =
      (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
        (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom := by
    rw [reassoc_of% key', hd, Category.comp_id]
  have r1 : (groupHom (baseChangeCompIso b c A).hom).hom.hom ≫
      (Over.pullback c).map ((Over.pullback b).map f) ≫
        (Over.pullback c).map (dualSchemeBaseChangeIso universality b A hA hAb).hom ≫
          (dualSchemeBaseChangeIso universality c ((baseChange b).obj A) hAb hAc).hom ≫
            dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).hom hAd hAc =
      (groupHom (baseChangeCompIso b c A).hom).hom.hom ≫
        (Over.pullback c).map ((Over.pullback b).map f) ≫
          (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
            (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom := by
    rw [s1]
  have r2 : (groupHom (baseChangeCompIso b c A).hom).hom.hom ≫
      (Over.pullback c).map ((Over.pullback b).map f) ≫
        (Over.pullbackComp c b).inv.app (dualScheme A hA) ≫
          (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom =
      (Over.pullback (c ≫ b)).map f ≫
        (dualSchemeBaseChangeIso universality (c ≫ b) A hA hAd).hom := by
    rw [reassoc_of% hn, reassoc_of% hc]
  simp only [dualBaseChangeMap_eq, Functor.map_comp, Category.assoc]
  exact (r1.trans r2).symm

end Langlands.AbelianScheme

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules GroupScheme.Tate

section Opens

variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)

include hU in
/-- Every geometric point factors through some member of a covering family of opens. -/
theorem exists_lift_of_opens (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ X) :
    ∃ (i : I) (s' : Spec (CommRingCat.of K) ⟶ (U i).toScheme), s' ≫ (U i).ι = s := by
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := ⟨(default : PrimeSpectrum K)⟩
  have hx : s x ∈ (⊤ : X.Opens) := trivial
  rw [← hU, TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hi⟩ := hx
  have hr : Set.range s ⊆ Set.range (U i).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y x]
    exact hi
  exact ⟨i, IsOpenImmersion.lift (U i).ι s hr, IsOpenImmersion.lift_fac _ _ _⟩

include hU in
/-- A Zariski-local property of the underlying morphism of a homomorphism of abelian schemes
holds if it holds after base change to every member of a covering family of opens. -/
theorem hom_prop_of_opens (Pr : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Pr]
    {A B : AbelianScheme X} (f : A ⟶ B)
    (h : ∀ i, Pr (hom ((AbelianScheme.baseChange (U i).ι).map f))) : Pr (hom f) := by
  apply IsZariskiLocalAtTarget.of_openCover ((X.openCoverOfIsOpenCover U hU).pullback₁ B.X.hom)
  intro i
  have sq := hom_baseChange_isPullback (U i).ι f
  change Pr (pullback.snd (hom f) (pullback.fst B.X.hom (U i).ι))
  rw [← sq.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso Pr _ _).mpr (h i)

include hU in
/-- Being an isogeny is local on the base. -/
theorem isIsogeny_of_opens {A B : AbelianScheme X} (f : A ⟶ B)
    (h : ∀ i, IsIsogeny ((AbelianScheme.baseChange (U i).ι).map f)) : IsIsogeny f :=
  (isIsogeny_iff f).2 ⟨hom_prop_of_opens U hU @IsFinite f (fun i => (h i).1),
    hom_prop_of_opens U hU @Flat f (fun i => (h i).2.1),
    hom_prop_of_opens U hU @Surjective f (fun i => (h i).2.2)⟩

include hU in
/-- Constant degree `d²` of an isogeny is local on the base. -/
theorem hasDegreeSquare_of_opens {A B : AbelianScheme X} (f : A ⟶ B) (hf : IsIsogeny f)
    {d : ℕ} (h : ∀ i, HasDegreeSquare ((AbelianScheme.baseChange (U i).ι).map f) d) :
    HasDegreeSquare f d := by
  have : IsFinite (hom f) := hf.1
  have : Flat (hom f) := hf.2.1
  intro y
  have hy : B.X.hom y ∈ (⊤ : X.Opens) := trivial
  rw [← hU, TopologicalSpace.Opens.mem_iSup] at hy
  obtain ⟨i, hi⟩ := hy
  obtain ⟨y', rfl⟩ : y ∈ Set.range (pullback.fst B.X.hom (U i).ι) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hi
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (hom_baseChange_isPullback (U i).ι f) y').symm.trans
    (h i y')

include hU in
/-- A constant relative dimension is local on the base. -/
theorem hasRelativeDimension_of_opens (A : AbelianScheme X) {g : ℕ}
    (h : ∀ i, ((AbelianScheme.baseChange (U i).ι).obj A).HasRelativeDimension g) :
    A.HasRelativeDimension g :=
  IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension g)
    (X.openCoverOfIsOpenCover U hU) (fun i => h i)

include hU in
/-- Fullness of an ordered tuple of torsion sections is local on the base. -/
theorem isFull_of_opens {A : AbelianScheme X} {g n : ℕ} (v : SectionTuple A g n)
    (h : ∀ i, IsFull (pullbackTuple (U i).ι v)) : IsFull v := by
  intro K _ _ s
  obtain ⟨i, s', rfl⟩ := exists_lift_of_opens U hU K s
  obtain ⟨bs, hbs⟩ := h i K s'
  refine ⟨bs.map (levelBaseChangeLinear A.toGrp (U i).ι (Over.mk s') n), fun k => ?_⟩
  rw [Module.Basis.map_apply, hbs k]
  exact fibreTuple_pullback (U i).ι v s' k

/-- A full-level structure on `A` from an ordered tuple of torsion sections whose
pullbacks to all members of a covering family of opens are full. -/
def FullLevel.ofOpens {A : AbelianScheme X} {g n : ℕ} (v : SectionTuple A g n)
    (h : ∀ i, IsFull (pullbackTuple (U i).ι v)) : FullLevel A g n :=
  ⟨v, isFull_of_opens U hU v h⟩

include hU in
/-- Being a polarization is local on the base: if the restriction of `lam` to every member
of a covering family of opens is a polarization for the pulled-back dual witness, then `lam`
is a polarization. -/
theorem DualWitness.isPolarization_of_opens (P : Prerequisites.{u}) {A : AbelianScheme X}
    (W : DualWitness A) (lam : A ⟶ W.dual P)
    (h : ∀ i, (W.pullback P (U i).ι).IsPolarization P
      (W.pullbackMap P (U i).ι (W.pullback P (U i).ι) lam)) :
    W.IsPolarization P lam := by
  refine ⟨?_, ?_⟩
  · apply isIsogeny_of_opens U hU
    intro i
    have h1 : IsIsogeny ((AbelianScheme.baseChange (U i).ι).map lam ≫
        (W.baseChangeIso P (U i).ι (W.pullback P (U i).ι)).hom) := (h i).1
    have h2 := h1.comp (isIsogeny_of_iso (W.baseChangeIso P (U i).ι (W.pullback P (U i).ι)).symm)
    rwa [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
  · intro K _ _ s
    obtain ⟨i, s', rfl⟩ := exists_lift_of_opens U hU K s
    have hAi := hasDualScheme_baseChange P.universality (U i).ι A W.hasDual
    have hi : HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
        ((AbelianScheme.baseChange s').obj ((AbelianScheme.baseChange (U i).ι).obj A))
        (hasDualScheme_baseChange P.universality s' _
          (hasDualScheme_baseChange P.universality (U i).ι A W.hasDual))
        (dualBaseChangeMap _ (hasDualScheme_baseChange P.universality (U i).ι A W.hasDual)
          P.universality s'
          (dualBaseChangeMap A W.hasDual P.universality (U i).ι (groupHom lam).hom.hom)) :=
      (congrArg (fun f : ((AbelianScheme.baseChange (U i).ι).obj A).X ⟶
          dualScheme _ (hasDualScheme_baseChange P.universality (U i).ι A W.hasDual) =>
          HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K _ _
            (dualBaseChangeMap _ _ P.universality s' f))
        (DualWitness.parameterMap_pullbackMap P W (U i).ι (W.pullback P (U i).ι) lam)).mp
        ((h i).2 K s')
    refine (congrArg (HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
      ((AbelianScheme.baseChange (s' ≫ (U i).ι)).obj A)
      (hasDualScheme_baseChange P.universality (s' ≫ (U i).ι) A W.hasDual))
      (dualBaseChangeMap_comp P.stability P.universality (U i).ι s' A W.hasDual
        (groupHom lam).hom.hom)).mpr ?_
    exact hasFieldAmpleMumfordPresentation_iso P.preservation P.square P.universality
      P.stability K (AbelianScheme.baseChangeCompIso (U i).ι s' A) _ _ _ hi

end Opens

end Langlands.AbelianScheme.PolarizedFiniteLevel
