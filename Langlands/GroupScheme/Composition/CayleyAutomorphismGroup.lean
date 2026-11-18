import Langlands.GroupScheme.Composition.CayleyGradingTorus
import Langlands.GroupScheme.Composition.SplitCayley
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # The automorphism group scheme of a Cayley datum as a closed subgroup of `GL₈` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CayleyDatum

variable {K : Type u} [Field K] (c : CayleyDatum K)

section Algebra

variable {A : Type u} [CommRing A] (φ : K →+* A)

/-- The failure of a matrix `g` to preserve the extended multiplication, as the bilinear map
`(x, y) ↦ g (x y) - (g x) (g y)`. -/
def multiplicationDefect (g : Matrix (Fin 8) (Fin 8) A) :
    CayleyVector A →ₗ[A] CayleyVector A →ₗ[A] CayleyVector A :=
  (c.multiplicationBilin φ).compr₂ g.mulVecLin -
    (c.multiplicationBilin φ).compl₁₂ g.mulVecLin g.mulVecLin

theorem multiplicationDefect_apply (g : Matrix (Fin 8) (Fin 8) A) (x y : CayleyVector A) :
    c.multiplicationDefect φ g x y =
      g.mulVec (c.multiplicationOver φ x y) -
        c.multiplicationOver φ (g.mulVec x) (g.mulVec y) := rfl

/-- The failure of a matrix `g` to fix the extended unit. -/
def unitDefect (g : Matrix (Fin 8) (Fin 8) A) : CayleyVector A :=
  g.mulVec (c.unitOver φ) - c.unitOver φ

/-- The automorphism equations hold exactly when the unit defect vanishes and the multiplication
defect vanishes on all pairs of standard basis vectors. -/
theorem isAutomorphismMatrix_iff (g : GL (Fin 8) A) :
    c.IsAutomorphismMatrix φ g ↔
      (∀ i, c.unitDefect φ (g : Matrix (Fin 8) (Fin 8) A) i = 0) ∧
        ∀ i j k, c.multiplicationDefect φ (g : Matrix (Fin 8) (Fin 8) A)
          (Pi.single j 1) (Pi.single k 1) i = 0 := by
  constructor
  · rintro ⟨hu, hm⟩
    refine ⟨fun i => ?_, fun i j k => ?_⟩
    · rw [unitDefect, hu, sub_self, Pi.zero_apply]
    · rw [multiplicationDefect_apply, hm, sub_self, Pi.zero_apply]
  · rintro ⟨hu, hm⟩
    refine ⟨?_, fun x y => ?_⟩
    · funext i
      exact sub_eq_zero.1 (hu i)
    · funext i
      apply sub_eq_zero.1
      rw [← Pi.sub_apply, ← multiplicationDefect_apply,
        SplitCayley.bilinear_apply_eq_sum]
      simp [hm]

/-- The identity matrix is an automorphism matrix. -/
theorem isAutomorphismMatrix_one : c.IsAutomorphismMatrix φ (1 : GL (Fin 8) A) := by
  refine ⟨?_, fun x y => ?_⟩ <;> simp

/-- Automorphism matrices are closed under products. -/
theorem IsAutomorphismMatrix.mul {g h : GL (Fin 8) A} (hg : c.IsAutomorphismMatrix φ g)
    (hh : c.IsAutomorphismMatrix φ h) : c.IsAutomorphismMatrix φ (g * h) := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh.1, hg.1]
  · simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hh.2, hg.2]

/-- Automorphism matrices are closed under inverses. -/
theorem IsAutomorphismMatrix.inv {g : GL (Fin 8) A} (hg : c.IsAutomorphismMatrix φ g) :
    c.IsAutomorphismMatrix φ g⁻¹ := by
  have hinv : ∀ v : CayleyVector A,
      (g : Matrix (Fin 8) (Fin 8) A).mulVec (((g⁻¹ : GL (Fin 8) A) :
        Matrix (Fin 8) (Fin 8) A).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hinj : ∀ v w : CayleyVector A,
      (g : Matrix (Fin 8) (Fin 8) A).mulVec v = (g : Matrix (Fin 8) (Fin 8) A).mulVec w →
        v = w := by
    intro v w h
    have h' := congrArg (((g⁻¹ : GL (Fin 8) A) : Matrix (Fin 8) (Fin 8) A).mulVec) h
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] using h'
  refine ⟨hinj _ _ ?_, fun x y => hinj _ _ ?_⟩
  · rw [hinv, hg.1]
  · rw [hinv, hg.2, hinv, hinv]

/-- The automorphism matrices with coefficients in `A`, as a subgroup of `GL₈(A)`. -/
def automorphismSubgroup : Subgroup (GL (Fin 8) A) where
  carrier := {g | c.IsAutomorphismMatrix φ g}
  one_mem' := c.isAutomorphismMatrix_one φ
  mul_mem' := fun hg hh => IsAutomorphismMatrix.mul c φ hg hh
  inv_mem' := fun hg => IsAutomorphismMatrix.inv c φ hg

theorem mem_automorphismSubgroup (g : GL (Fin 8) A) :
    g ∈ c.automorphismSubgroup φ ↔ c.IsAutomorphismMatrix φ g :=
  Iff.rfl

/-- Both defects commute with every change of coefficients. -/
theorem map_unitDefect {B : Type u} [CommRing B] (f : A →+* B)
    (g : Matrix (Fin 8) (Fin 8) A) (i : Fin 8) :
    f (c.unitDefect φ g i) = c.unitDefect (f.comp φ) (g.map f) i := by
  simp only [unitDefect, Pi.sub_apply, map_sub, RingHom.map_mulVec, unitOver,
    RingHom.comp_apply]
  rfl

theorem map_multiplicationOver {B : Type u} [CommRing B] (f : A →+* B) (x y : CayleyVector A)
    (i : Fin 8) :
    f (c.multiplicationOver φ x y i) =
      c.multiplicationOver (f.comp φ) (fun l => f (x l)) (fun l => f (y l)) i := by
  simp [multiplicationOver, map_sum, map_mul]

theorem map_multiplicationDefect {B : Type u} [CommRing B] (f : A →+* B)
    (g : Matrix (Fin 8) (Fin 8) A) (x y : CayleyVector A) (i : Fin 8) :
    f (c.multiplicationDefect φ g x y i) =
      c.multiplicationDefect (f.comp φ) (g.map f) (fun l => f (x l)) (fun l => f (y l)) i := by
  have h1 : (⇑f ∘ c.multiplicationOver φ x y) =
      c.multiplicationOver (f.comp φ) (fun l => f (x l)) (fun l => f (y l)) :=
    funext fun l => c.map_multiplicationOver φ f x y l
  have h2 : ∀ v : CayleyVector A,
      (fun l => f (g.mulVec v l)) = (g.map f).mulVec (fun l => f (v l)) :=
    fun v => funext fun l => RingHom.map_mulVec f g v l
  rw [multiplicationDefect_apply, multiplicationDefect_apply, Pi.sub_apply, Pi.sub_apply,
    map_sub, RingHom.map_mulVec, map_multiplicationOver, h1, h2 x, h2 y]

end Algebra

/-! ### The cut-out closed subgroup scheme -/

section Scheme

open Langlands.GroupScheme.GeneralLinear

/-- The published smoothness of the coordinate ring of `GL₈` gives finite type of `GL₈` over
`K`. -/
local instance locallyOfFiniteType_generalLinear :
    LocallyOfFiniteType (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of K)
      (CoordinateRing (Fin 8) (CommRingCat.of K)))))
  apply HasRingHomProperty.Spec_iff.mpr
  let := coordinateRing_smooth (Fin 8) (CommRingCat.of K)
  exact RingHom.finiteType_algebraMap.mpr inferInstance

local instance isAffineHom_generalLinear :
    IsAffineHom (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom :=
  isAffineHom_groupScheme (Fin 8) (CommRingCat.of K)

/-- The coordinate ring of `GL₈` over `K`. -/
local notation "𝒪" => GeneralLinear.CoordinateRing (Fin 8) (CommRingCat.of K)

/-- The universal invertible matrix over the coordinate ring of `GL₈`. -/
local notation "𝔤" => GeneralLinear.universal (Fin 8) (CommRingCat.of K)

/-- The defining equations of the automorphism group at the universal matrix: the coordinates of
the unit defect and of the multiplication defect on pairs of standard basis vectors. -/
def automorphismGenerators : Set 𝒪 :=
  {b | (∃ i, c.unitDefect (algebraMap (CommRingCat.of K) 𝒪)
        ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) i = b) ∨
    ∃ i j k, c.multiplicationDefect (algebraMap (CommRingCat.of K) 𝒪)
        ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) (Pi.single j 1) (Pi.single k 1) i = b}

/-- The ideal of the coordinate ring of `GL₈` cutting out the automorphism group. -/
def automorphismIdeal : Ideal 𝒪 :=
  Ideal.span c.automorphismGenerators

/-- The automorphism subgroups of `GL₈(A)` for all commutative `K`-algebras `A`. -/
def automorphismFamily :
    ∀ A : CommAlgCat.{u} (CommRingCat.of K), Subgroup ((functor (Fin 8) (CommRingCat.of K)).obj A) :=
  fun A => c.automorphismSubgroup (algebraMap (CommRingCat.of K) A)

/-- The classifying algebra map of `g` sends each universal defect to the corresponding defect
of `g`. -/
theorem classify_unitDefect {S : Type u} [CommRing S] [Algebra (CommRingCat.of K) S]
    (g : GL (Fin 8) S) (i : Fin 8) :
    classify (R := CommRingCat.of K) g
        (c.unitDefect (algebraMap (CommRingCat.of K) 𝒪)
          ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) i) =
      c.unitDefect (algebraMap (CommRingCat.of K) S) (g : Matrix (Fin 8) (Fin 8) S) i := by
  have h := c.map_unitDefect (algebraMap (CommRingCat.of K) 𝒪)
    (classify (R := CommRingCat.of K) g).toRingHom
    ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) i
  have hφ : (classify (R := CommRingCat.of K) g).toRingHom.comp
      (algebraMap (CommRingCat.of K) 𝒪) = algebraMap (CommRingCat.of K) S :=
    (classify (R := CommRingCat.of K) g).comp_algebraMap
  have hg : ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪).map
      (classify (R := CommRingCat.of K) g).toRingHom = (g : Matrix (Fin 8) (Fin 8) S) := by
    ext a b
    rw [Matrix.map_apply, universal_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact classify_entry g a b
  rw [hφ, hg] at h
  exact h

theorem classify_multiplicationDefect {S : Type u} [CommRing S] [Algebra (CommRingCat.of K) S]
    (g : GL (Fin 8) S) (i j k : Fin 8) :
    classify (R := CommRingCat.of K) g
        (c.multiplicationDefect (algebraMap (CommRingCat.of K) 𝒪)
          ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) (Pi.single j 1) (Pi.single k 1) i) =
      c.multiplicationDefect (algebraMap (CommRingCat.of K) S) (g : Matrix (Fin 8) (Fin 8) S)
        (Pi.single j 1) (Pi.single k 1) i := by
  have h := c.map_multiplicationDefect (algebraMap (CommRingCat.of K) 𝒪)
    (classify (R := CommRingCat.of K) g).toRingHom
    ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪) (Pi.single j 1) (Pi.single k 1) i
  have hφ : (classify (R := CommRingCat.of K) g).toRingHom.comp
      (algebraMap (CommRingCat.of K) 𝒪) = algebraMap (CommRingCat.of K) S :=
    (classify (R := CommRingCat.of K) g).comp_algebraMap
  have hg : ((𝔤 : GL (Fin 8) 𝒪) : Matrix (Fin 8) (Fin 8) 𝒪).map
      (classify (R := CommRingCat.of K) g).toRingHom = (g : Matrix (Fin 8) (Fin 8) S) := by
    ext a b
    rw [Matrix.map_apply, universal_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact classify_entry g a b
  have hs : ∀ m : Fin 8, (fun l => (classify (R := CommRingCat.of K) g).toRingHom
      ((Pi.single m (1 : 𝒪) : Fin 8 → 𝒪) l)) = Pi.single m 1 := by
    intro m
    funext l
    by_cases hl : l = m
    · subst hl; simp
    · simp [hl]
  rw [hφ, hg, hs, hs] at h
  exact h

/-- A matrix lies in the automorphism subgroup exactly when its classifying algebra map kills
`automorphismIdeal`. -/
theorem mem_automorphismSubgroup_iff_classify {S : Type u} [CommRing S]
    [Algebra (CommRingCat.of K) S] (g : GL (Fin 8) S) :
    g ∈ c.automorphismSubgroup (algebraMap (CommRingCat.of K) S) ↔
      ∀ b ∈ c.automorphismIdeal, classify (R := CommRingCat.of K) g b = 0 := by
  rw [mem_automorphismSubgroup, isAutomorphismMatrix_iff]
  constructor
  · rintro ⟨hu, hm⟩ b hb
    have hle : c.automorphismIdeal ≤ RingHom.ker (classify (R := CommRingCat.of K) g) := by
      rw [automorphismIdeal, Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, j, k, rfl⟩)
      · rw [SetLike.mem_coe, RingHom.mem_ker, classify_unitDefect]
        exact hu i
      · rw [SetLike.mem_coe, RingHom.mem_ker, classify_multiplicationDefect]
        exact hm i j k
    exact hle hb
  · intro h
    refine ⟨fun i => ?_, fun i j k => ?_⟩
    · rw [← classify_unitDefect]
      exact h _ (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
    · rw [← classify_multiplicationDefect]
      exact h _ (Ideal.subset_span (Or.inr ⟨i, j, k, rfl⟩))

/-- The automorphism subgroups are cut out by `automorphismIdeal`. -/
theorem isCutOutBy_automorphismIdeal :
    Corepresented.IsCutOutBy (corepresentableBy (Fin 8) (CommRingCat.of K))
      c.automorphismFamily c.automorphismIdeal := fun A g =>
  c.mem_automorphismSubgroup_iff_classify (S := A) g

/-- The automorphism group scheme of a Cayley datum: the closed subgroup scheme of `GL₈` whose
points with values in `A` are the invertible matrices fixing the unit and preserving the
multiplication extended to `A`. -/
abbrev automorphismGroup : GroupScheme (Spec (CommRingCat.of K)) :=
  Corepresented.cutGroupScheme c.isCutOutBy_automorphismIdeal

/-- The inclusion of the automorphism group scheme into `GL₈`. -/
def automorphismInclusion :
    c.automorphismGroup ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K) :=
  Corepresented.cutHom c.isCutOutBy_automorphismIdeal

/-- The inclusion of the automorphism group scheme realizes the full automorphism functor of the
Cayley datum. -/
theorem isAutomorphismRepresentation_automorphismInclusion :
    c.IsAutomorphismRepresentation c.automorphismInclusion := by
  refine ⟨Corepresented.isClosedSubgroup_cutHom c.isCutOutBy_automorphismIdeal, fun T g => ?_⟩
  unfold automorphismInclusion
  rw [Corepresented.range_cutHom]
  exact Corepresented.mem_cutSubgroupFunctor c.isCutOutBy_automorphismIdeal

instance isAffineHom_automorphismGroup : IsAffineHom c.automorphismGroup.X.hom := by
  have h : IsAffineHom (c.automorphismInclusion.hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom) := by
    have : IsClosedImmersion c.automorphismInclusion.hom.hom.left :=
      Corepresented.isClosedImmersion_cutHom c.isCutOutBy_automorphismIdeal
    infer_instance
  simpa only [Over.w] using h

instance locallyOfFiniteType_automorphismGroup :
    LocallyOfFiniteType c.automorphismGroup.X.hom := by
  have h : LocallyOfFiniteType (c.automorphismInclusion.hom.hom.left ≫
      (GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)).X.hom) := by
    have : IsClosedImmersion c.automorphismInclusion.hom.hom.left :=
      Corepresented.isClosedImmersion_cutHom c.isCutOutBy_automorphismIdeal
    infer_instance
  simpa only [Over.w] using h

end Scheme

end CayleyDatum

end Langlands.GroupScheme
