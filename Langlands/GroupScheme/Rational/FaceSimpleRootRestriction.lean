import Langlands.GroupScheme.Rational.AbsoluteRootRestriction
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.CocenterCoweightDescent
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.LatticeBaseInvariants
import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Simple roots of a coweight face restrict to simple relative roots

Let `f : S ⟶ T` be the largest split subtorus of a torus `T`, embedded in `G`
by `j` and split by a finite Galois extension `E/k`, and let `ν` be a generic
cocharacter of `S`. For any face of the absolute root datum adapted to the
base change of `ν`, a simple root not vanishing on `ν` restricts to a simple
relative root, while a root vanishing on `ν` restricts to zero.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.FaceSimpleRootRestriction

open LinearAlgebra.RootDatumCoweightFace LinearAlgebra.RootDatumFaceHeight

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k E
local notation "T_E" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "S_E" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "f_E" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) f
local notation "j_E" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j

local instance : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

local instance : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- The pairing of a character with the base change of a composite cocharacter
is the pairing of its restriction. -/
theorem latticePairing_baseChange_comp (χ : characterLattice T_E)
    (ν : cocharacterLattice S) :
    latticePairing T_E χ (cocharacterLattice.baseChange b T (ν ≫ f)) =
      latticePairing S_E (f_E ≫ χ) (cocharacterLattice.baseChange b S ν) := by
  rw [latticePairing_apply, latticePairing_apply, cocharacterLattice.baseChange_comp,
    Category.assoc]

/-- For a generic cocharacter, a root of the extended torus vanishing on its
base change restricts to zero on the extended split torus. -/
theorem restrict_eq_zero_of_pairing_eq_zero
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_E).toGrp)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
    {χ : characterLattice T_E} (hχ : χ ∈ roots j_E)
    (h0 : latticePairing T_E χ (cocharacterLattice.baseChange b T (ν ≫ f)) = 0) :
    f_E ≫ χ = 0 := by
  obtain ⟨a, ha⟩ := (hS.characterLattice_baseChange_bijective b S).surjective (f_E ≫ χ)
  by_cases ha0 : a = 0
  · rw [← ha, ha0, map_zero]
  · exfalso
    have hmem : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
      (mem_roots_iff_exists_splittingField_restriction hS hT f j a).mpr
        ⟨ha0, χ, hχ, ha.symm⟩
    apply hν a hmem
    rw [← latticePairing_baseChange b S a ν, ha, ← latticePairing_baseChange_comp]
    exact h0

section Face

variable [FiniteDimensional k E] [IsGalois k E]
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]
  {J : Type u} [Fintype J]
  {P : RootDatum J (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
    (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))}
  [P.IsReduced]
  (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp)
  (hj : IsClosedImmersion
    ((GroupScheme.baseChange (algebraBaseMap k E)).map j).hom.hom.left)
  (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k E)).map j) P)
  (ν : cocharacterLattice S)

omit [FiniteDimensional k E] [IsGalois k E] [IsAffineHom T.toGrp.X.hom]
  [LocallyOfFiniteType T.toGrp.X.hom] in
/-- The face height of a face adapted to the base change of a cocharacter is
invariant under the Galois action on the root span. -/
theorem faceHeight_galois {ν' : cocharacterLattice T_E}
    (hν' : cocharacterLattice.baseChange b T (ν ≫ f) = ν') (C : Face P ν')
    (σ : E ≃ₐ[k] E) (x : P.rootSpan ℤ) :
    faceHeight C.base ν'
        (rootSpanMap (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E j hT hj hP σ)
          x) =
      faceHeight C.base ν' x := by
  have := hj
  have : Finite (weylImage (T := T_E) j_E) := splitTorusWeylImageFinite E _ _ hT _ hj
  have : Finite P.weylGroup := hP.finite_abstractWeylGroup
  have hδ : (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E j hT hj hP σ).coweightEquiv
      ν' = ν' := by
    subst hν'
    change cocharacterLattice.galoisRepresentation k E T σ⁻¹ _ = _
    exact cocharacterLattice.galoisRepresentation_baseChange k E T σ⁻¹ _
  have h := faceHeight_comp_rootSpanMap (face_dominant C) (C.correction _ hδ)
  exact LinearMap.congr_fun h x

include hT hj hP in
/-- The face height vanishes on root-span elements restricting to zero on the
largest split subtorus. -/
theorem faceHeight_eq_zero_of_restrict_eq_zero
    (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f)) {ν' : cocharacterLattice T_E}
    (hν' : cocharacterLattice.baseChange b T (ν ≫ f) = ν') (C : Face P ν')
    (x : P.rootSpan ℤ) (hx : f_E ≫ (x : characterLattice T_E) = 0) :
    faceHeight C.base ν' x = 0 := by
  classical
  let _ : Fintype (E ≃ₐ[k] E) := Fintype.ofFinite _
  have hTt : IsTorus T.toGrp := ⟨E, inferInstance, inferInstance, hT⟩
  have hzero := hf.galoisOrbitSum_character_eq_zero E hTt _ hx
  have hsum : ∑ σ : E ≃ₐ[k] E,
      rootSpanMap (IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus k E j hT hj hP σ) x =
        0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero, ← hzero]
    rfl
  have h := congrArg (faceHeight C.base ν') hsum
  rw [map_sum, map_zero,
    Finset.sum_congr rfl (fun σ _ => faceHeight_galois k E f j hT hj hP ν hν' C σ x),
    Finset.sum_const, Finset.card_univ] at h
  exact (smul_eq_zero.mp h).resolve_left Fintype.card_ne_zero

include hT hj hP in
/-- **Simple restriction.** A simple root of a face base not vanishing on the
base change of a generic cocharacter `ν` restricts to a simple relative root
for `ν`. -/
theorem restrict_mem_simpleRelativeRoots
    (hS : IsSplitTorus S.toGrp)
    (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f)) {ν' : cocharacterLattice T_E}
    (hν' : cocharacterLattice.baseChange b T (ν ≫ f) = ν') (C : Face P ν')
    {β : J} (hβ : β ∈ C.base.support) (hne : P.root' β ν' ≠ 0)
    {a : characterLattice S} (ha : f_E ≫ P.root β = characterLattice.baseChange b S a) :
    a ∈ simpleRelativeRoots (CommGroupScheme.groupHom f ≫ j) ν := by
  have hpair (m : J) {c : characterLattice S}
      (hc : f_E ≫ P.root m = characterLattice.baseChange b S c) :
      P.root' m ν' = latticePairing S c ν := by
    change P.toLinearMap (P.root m) ν' = _
    rw [hP.1, ← hν', latticePairing_baseChange_comp, hc, latticePairing_baseChange]
  have hroot (m : J) : P.root m ∈ roots j_E := by
    rw [← hP.2.1]
    exact ⟨m, rfl⟩
  have hdom := face_dominant C
  have hpos : 0 < P.root' β ν' := lt_of_le_of_ne (hdom β hβ) (Ne.symm hne)
  have hlift : ∀ c ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j),
      ∃ m : J, f_E ≫ P.root m = characterLattice.baseChange b S c := by
    intro c hc
    obtain ⟨-, χ, hχ, hχc⟩ :=
      (mem_roots_iff_exists_splittingField_restriction hS hT f j c).mp hc
    rw [← hP.2.1] at hχ
    obtain ⟨m, rfl⟩ := hχ
    exact ⟨m, hχc⟩
  have hapos : 0 < latticePairing S a ν := by rwa [← hpair β ha]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hapos
  refine ⟨⟨(mem_roots_iff_exists_splittingField_restriction hS hT f j a).mpr
    ⟨ha0, P.root β, hroot β, ha⟩, hapos⟩, ?_⟩
  rintro ⟨a₁, ⟨ha₁, hp₁⟩, a₂, ⟨ha₂, hp₂⟩, rfl⟩
  obtain ⟨m₁, hm₁⟩ := hlift a₁ ha₁
  obtain ⟨m₂, hm₂⟩ := hlift a₂ ha₂
  have h₁ := one_le_faceHeight_root_of_pos hdom m₁ (by rw [hpair m₁ hm₁]; exact hp₁)
  have h₂ := one_le_faceHeight_root_of_pos hdom m₂ (by rw [hpair m₂ hm₂]; exact hp₂)
  have hβh := faceHeight_simple C.base ν' β hβ
  rw [ite_eq_right_iff.mpr (fun h => absurd h hne)] at hβh
  have hy := faceHeight_eq_zero_of_restrict_eq_zero k E f j hT hj hP ν hf hν' C
    (P.rootSpanMem ℤ β - P.rootSpanMem ℤ m₁ - P.rootSpanMem ℤ m₂) (by
      change f_E ≫ (P.root β - P.root m₁ - P.root m₂) = 0
      rw [Preadditive.comp_sub, Preadditive.comp_sub, ha, hm₁, hm₂, map_add]
      abel)
  rw [map_sub, map_sub, hβh] at hy
  omega

include hT hj hP in
/-- **Signs on a standard cocharacter.** Let `β` be a simple root of a face
base adapted to the base change of the generic cocharacter `ν`, restricting to
`a` on the split torus, and let `ζ` be a standard cocharacter for `{α}`. Then
`β` pairs nonnegatively with the base change of `ζ`, and vanishes on it exactly
when `β` vanishes on the base change of `ν` or `a = α`. -/
theorem root'_standard (hS : IsSplitTorus S.toGrp)
    (hf : IsLargestSplitSubtorus (CommGroupScheme.groupHom f))
    (hν : IsGenericCocharacter (CommGroupScheme.groupHom f ≫ j) ν)
    {ν' : cocharacterLattice T_E}
    (hν' : cocharacterLattice.baseChange b T (ν ≫ f) = ν') (C : Face P ν')
    {β : J} (hβ : β ∈ C.base.support)
    {a : characterLattice S} (ha : f_E ≫ P.root β = characterLattice.baseChange b S a)
    {α : characterLattice S} {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter (CommGroupScheme.groupHom f ≫ j) ν {α} ζ) :
    0 ≤ P.root' β (cocharacterLattice.baseChange b T (ζ ≫ f)) ∧
      (P.root' β (cocharacterLattice.baseChange b T (ζ ≫ f)) = 0 ↔
        P.root' β ν' = 0 ∨ a = α) := by
  have hpair : P.root' β (cocharacterLattice.baseChange b T (ζ ≫ f)) =
      latticePairing S a ζ := by
    change P.toLinearMap (P.root β) _ = _
    rw [hP.1, latticePairing_baseChange_comp, ha, latticePairing_baseChange]
  rw [hpair]
  by_cases h0 : P.root' β ν' = 0
  · have hroot : P.root β ∈ roots j_E := by
      rw [← hP.2.1]
      exact ⟨β, rfl⟩
    have hz := restrict_eq_zero_of_pairing_eq_zero k E f j hS hT ν hν hroot (by
      rw [hν', ← hP.1]
      exact h0)
    have ha0 : a = 0 := (hS.characterLattice_baseChange_bijective b S).injective (by
      rw [← ha, hz, map_zero])
    subst ha0
    simp [h0]
  · have hA := restrict_mem_simpleRelativeRoots k E f j hT hj hP ν hS hf hν' C hβ h0 ha
    by_cases haα : a = α
    · subst haα
      have h := hζ.2.1 a (Set.mem_singleton a)
      exact ⟨h.ge, iff_of_true h (Or.inr rfl)⟩
    · have h := hζ.2.2 a hA (by simpa using haα)
      exact ⟨h.le, iff_of_false h.ne' (by simp [h0, haα])⟩

end Face

end Langlands.GroupScheme.FaceSimpleRootRestriction
