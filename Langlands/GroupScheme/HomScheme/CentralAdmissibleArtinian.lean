import Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence
import Langlands.AlgebraicGeometry.SmoothNilIdealSections
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianNilpotentLifting
import Langlands.GroupScheme.HomScheme.CentralAdmissiblePresheaf
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.Torus.CentralInfinitesimalRigidityReduction
import Langlands.GroupScheme.Torus.DiagonalizableActionNilpotentRigidity
import Langlands.GroupScheme.Torus.MultiplicativeTypeNilpotentHom
import Langlands.GroupScheme.Torus.NilpotentConjugationAction
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType

/-! # Local Artinian infinitesimal bijectivity for central closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

section NilpotentQuotient

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "Q" => baseChange (Spec.algebraMap A (A ⧸ I))

private theorem range_le_of_nilpotent_range_eq (hI : IsNilpotent I)
    {G H K : GroupScheme (Spec (CommRingCat.of A))} (j : H ⟶ G) (k : K ⟶ G)
    (hj : IsClosedSubgroup j) (hk : IsClosedSubgroup k)
    (hH : RelativeTorus.IsTorus H) (hK : RelativeTorus.IsTorus K) (hc : IsCentral j)
    (he : range ((Q).map j) = range ((Q).map k)) : range j ≤ range k := by
  let j₀ := (Q).map j
  let k₀ := (Q).map k
  have : IsClosedImmersion j₀.hom.hom.left := IsClosedSubgroup.baseChange _ hj
  have : IsClosedImmersion k₀.hom.hom.left := IsClosedSubgroup.baseChange _ hk
  let hj₀ : (range j₀).IsRepresentedBy j₀ := ⟨Over.mono_of_mono_left _, rfl⟩
  let hk₀ : (range j₀).IsRepresentedBy k₀ := ⟨Over.mono_of_mono_left _, he.symm⟩
  let e₀ := hj₀.isoOfIsRepresentedBy hk₀
  have hmp : RelativeMultiplicativeType.IsMultiplicativeType H := hH.isMultiplicativeType
  let r := Spec.algebraMap A (A ⧸ I)
  have : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
      Ideal.Quotient.mk_surjective
  have : Surjective r :=
    Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence.spec_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (by simpa using hI)
  obtain ⟨m, hm⟩ := (hmp.baseChange_hom_bijective_of_surjective_closedImmersion
    hK.isMultiplicativeType r).surjective e₀.hom
  have heq : (Q).map j = (Q).map (m ≫ k) := by
    change (Q).map m = e₀.hom at hm
    rw [Functor.map_comp, hm]
    exact (hj₀.isoOfIsRepresentedBy_hom_comp hk₀).symm
  have h : j = m ≫ k :=
    CentralInfinitesimalRigidity.multiplicativeType_central_uniqueness_of_actionRigidity
      (fun _ _ _ _ a J hJ ha => a.hom_eq_snd_of_nilpotent_quotient J hJ ha)
      A I hI G H j (m ≫ k) hmp heq (hc.baseChange _)
  intro T x hx
  obtain ⟨t, ht⟩ := hx
  refine ⟨t ≫ m.hom.hom, ?_⟩
  change t ≫ j.hom.hom = x at ht
  change (t ≫ m.hom.hom) ≫ k.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, ← h, ht]

/-- Two central closed tori whose ranges coincide after nilpotent reduction
have equal ranges over the original base. -/
theorem central_range_eq_of_nilpotent_range_eq (hI : IsNilpotent I)
    {G H K : GroupScheme (Spec (CommRingCat.of A))} (j : H ⟶ G) (k : K ⟶ G)
    (hj : IsClosedSubgroup j) (hk : IsClosedSubgroup k)
    (hH : RelativeTorus.IsTorus H) (hK : RelativeTorus.IsTorus K)
    (hcj : IsCentral j) (hck : IsCentral k)
    (he : range ((Q).map j) = range ((Q).map k)) : range j = range k :=
  le_antisymm (range_le_of_nilpotent_range_eq I hI j k hj hk hH hK hcj he)
    (range_le_of_nilpotent_range_eq I hI k j hk hj hK hH hck he.symm)

/-- A closed torus over a local nilpotent quotient of an affine smooth group
lifts to an actual closed torus of that group. -/
theorem exists_closedTorus_lift_of_affine [IsLocalRing A] (hI : IsNilpotent I)
    (G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (F : SubgroupFunctor ((Q).obj G)) (hF : IsAdmissible F) :
    ∃ (T : GroupScheme (Spec (CommRingCat.of A))) (i : T ⟶ G),
      IsClosedSubgroup i ∧ RelativeTorus.IsTorus T ∧ range ((Q).map i) = F := by
  obtain ⟨M, H, j, hj, hH, hu, hM⟩ := smoothTorusSubgroupRepresentability _ G
  let r := Spec.algebraMap A (A ⧸ I)
  obtain ⟨s, hs, -⟩ := hu (Over.mk r) F hF
  have hnil : I ≤ nilradical A := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact mem_nilradical.mpr ⟨n, by
      have he := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at he
      exact he⟩
  obtain ⟨t, ht, ht₀⟩ := Langlands.AlgebraicGeometry.SmoothNilIdealSections.exists_lift_of_nil_ideal
    M.hom I hnil s.left s.w
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let a : W ⟶ M := Over.homMk t ht
  let b : Over.mk r ⟶ W := Over.homMk r (Category.comp_id r)
  have hab : b ≫ a = s := Over.OverMorphism.ext ht₀
  let j₁ := familyHom j a
  let i := j₁ ≫ (baseChangeIdIso G).hom
  have hclosed : IsClosedImmersion j₁.hom.hom.left := isClosedSubgroup_familyHom j hj a
  refine ⟨_, i, ?_, hH.baseChange a.left, ?_⟩
  · change IsClosedImmersion (j₁.hom.hom.left ≫ (baseChangeIdIso G).hom.hom.hom.left)
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  · have hcmp : (Q).map i = familyHom j₁ b := by
      rw [Functor.map_comp]
      change (Q).map j₁ ≫ (Q).map (baseChangeIdIso G).hom =
        (Q).map j₁ ≫ (Descent.pullbackComparison W.hom b.left r b.w G).hom
      congr 1
      apply Grp.hom_ext
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · rw [Descent.pullbackComparison_hom_fst]
        have e₁ : ((baseChange W.hom).obj G).X.hom ≫ 𝟙 _ =
            (baseChangeIdIso G).hom.hom.hom.left ≫ G.X.hom :=
          (Category.comp_id _).trans (Over.w (baseChangeIdIso G).hom.hom.hom).symm
        have e₂ : r ≫ 𝟙 _ = 𝟙 _ ≫ r := by simp
        change pullback.map _ _ _ _ (baseChangeIdIso G).hom.hom.hom.left (𝟙 _) (𝟙 _) e₁ e₂ ≫ _ = _
        rw [pullback.map, pullback.lift_fst, baseChangeIdIso_hom_left]
        rfl
      · exact (((Q).map (baseChangeIdIso G).hom).hom.hom.w).trans
          ((Descent.pullbackComparison W.hom b.left r b.w G).hom.hom.hom.w).symm
    rw [hcmp, ← evaluate, evaluate_comp, hab, hs]

end NilpotentQuotient

variable {S : Scheme.{u}}

set_option maxHeartbeats 800000 in
private theorem central_quotient_bijective (G : GroupScheme S) [Smooth G.X.hom]
    {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : IsNilpotent I)
    (f : Spec (CommRingCat.of A) ⟶ S) [IsAffineHom ((baseChange f).obj G).X.hom] :
    Function.Bijective ((smallCentralAdmissiblePresheaf G).map
      (algebraOverBase f (A ⧸ I)).op) := by
  let M := Over.mk f
  let T := algebraOver f (A ⧸ I)
  let a : T ⟶ M := algebraOverBase f (A ⧸ I)
  let r := Spec.algebraMap A (A ⧸ I)
  let H := (baseChange f).obj G
  have : Smooth H.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  let c : (baseChange r).obj H ≅ (baseChange T.hom).obj G :=
    Descent.pullbackComparison M.hom a.left T.hom a.w G
  constructor
  · intro x y hxy
    let j := admissibleRepresentative (smallAdmissibleEquiv G M x.val)
    let k := admissibleRepresentative (smallAdmissibleEquiv G M y.val)
    have h := congrArg (fun s => (smallAdmissibleEquiv G T s.val).val) hxy
    change (smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op x.val)).val =
      (smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op y.val)).val at h
    rw [smallAdmissibleEquiv_map a x.val, smallAdmissibleEquiv_map a y.val,
      restrict_eq_evaluate _ j.hom j.represents.2 a,
      restrict_eq_evaluate _ k.hom k.represents.2 a] at h
    have hred : range ((baseChange r).map j.hom) = range ((baseChange r).map k.hom) := by
      change range ((baseChange r).map j.hom ≫ c.hom) =
        range ((baseChange r).map k.hom ≫ c.hom) at h
      simpa only [range_comp_iso, ← comap_comp, Iso.hom_inv_id, comap_id]
        using congrArg (SubgroupFunctor.comap c.hom) h
    have hjc : IsCentral j.hom := (mem_centralAdmissible_iff x.val).mp x.property
    have hkc : IsCentral k.hom := (mem_centralAdmissible_iff y.val).mp y.property
    have hfull := central_range_eq_of_nilpotent_range_eq I hI j.hom k.hom
      j.closed k.closed j.torus k.torus hjc hkc hred
    apply Subtype.ext
    apply (smallAdmissibleEquiv G M).injective
    exact Subtype.ext (j.represents.2.symm.trans (hfull.trans k.represents.2))
  · intro z
    let d := admissibleRepresentative (smallAdmissibleEquiv G T z.val)
    let j₀ := d.hom ≫ c.inv
    have hclosed₀ : IsClosedSubgroup j₀ := by
      have : IsClosedImmersion d.hom.hom.hom.left := d.closed
      change IsClosedImmersion (d.hom.hom.hom.left ≫ c.inv.hom.hom.left)
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      infer_instance
    obtain ⟨K, j, hj, hK, hred⟩ := exists_closedTorus_lift_of_affine I hI H
      (range j₀) (isAdmissible_range j₀ hclosed₀ d.torus)
    have hEval : evaluate j a = (smallAdmissibleEquiv G T z.val).val := by
      change range ((baseChange r).map j ≫ c.hom) = _
      change range ((baseChange r).map j) = range j₀ at hred
      have h₀ : range j₀ = comap c.hom (range d.hom) := by
        change range (d.hom ≫ c.symm.hom) = comap c.symm.inv (range d.hom)
        rw [range_comp_iso]
      rw [range_comp_iso, hred, h₀, ← comap_comp, Iso.inv_hom_id, comap_id]
      exact d.represents.2
    have hcentral₀ : IsCentral ((baseChange a.left).map j) := by
      apply (central_evaluate_iff j a).mp
      rw [hEval]
      exact z.property
    have hcentral : IsCentral j := NilpotentConjugation.isCentral_of_isMultiplicativeType
      hK.isMultiplicativeType j I hI hcentral₀
    let F : AdmissibleSubgroup ((baseChange M.hom).obj G) := ⟨range j, isAdmissible_range j hj hK⟩
    let x := (smallAdmissibleEquiv G M).symm F
    have hx : x ∈ (centralAdmissibleSubfunctor G).obj (op M) := by
      change (smallAdmissibleEquiv G M x).val ≤ center _
      rw [Equiv.apply_symm_apply]
      exact (isCentral_iff_range_le_center _).mp hcentral
    refine ⟨⟨x, hx⟩, Subtype.ext ((smallAdmissibleEquiv G T).injective (Subtype.ext ?_))⟩
    change (smallAdmissibleEquiv G T ((smallAdmissiblePresheaf G).map a.op x)).val = _
    rw [smallAdmissibleEquiv_map a x, Equiv.apply_symm_apply]
    exact (restrict_eq_evaluate F j rfl a).trans hEval

/-- Smoothness and affineness on local Artinian tests suffice for infinitesimal
bijectivity of the central closed torus-subgroup presheaf. -/
def CentralAdmissibleArtinianStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom],
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (f : Spec (CommRingCat.of A) ⟶ S), IsAffineHom ((baseChange f).obj G).X.hom) →
    ArtinianNilpotentBijective (smallCentralAdmissiblePresheaf G)

/-- Pass from quotient tests to arbitrary nilpotent surjections by the actual
isomorphism of the quotient ring with the target ring. -/
theorem smallCentralAdmissiblePresheaf_artinianNilpotentBijective :
    CentralAdmissibleArtinianStatement.{u} := by
  intro S G _ h A B _ _ _ _ q hq hnil f g w
  let I := RingHom.ker q
  let r := Ideal.Quotient.mk I
  let a := algebraOverBase f (A ⧸ I)
  let e : A ⧸ I ≃+* B := RingHom.quotientKerEquivOfSurjective hq
  have he : e.toRingHom.comp r = q := by
    ext x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hq x
  let eS := Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op
  have hS : eS.hom ≫ (algebraOver f (A ⧸ I)).hom = g := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom r) ≫ f = g
    rw [GenericLift.spec_comp₁₁ he, w]
  let b : Over.mk g ≅ algebraOver f (A ⧸ I) := Over.isoMk eS hS
  have hab : b.hom ≫ a = GenericLift.rhom q w := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom r) =
      Spec.map (CommRingCat.ofHom q)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]
  have : IsAffineHom ((baseChange f).obj G).X.hom := h A f
  let P := smallCentralAdmissiblePresheaf G
  rw [← hab, op_comp, Functor.map_comp]
  exact ((CategoryTheory.isIso_iff_bijective (P.map b.hom.op)).mp inferInstance).comp
    (central_quotient_bijective G I hnil f)

end Langlands.GroupScheme.TorusSubgroupModuli
