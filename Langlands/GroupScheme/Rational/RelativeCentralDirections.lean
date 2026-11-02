import Langlands.GroupScheme.Rational.RelativeRank
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction
import Langlands.Geometry.Building.RealTorusAction

/-! # Full-lattice relative Weyl actions and actual central-direction interfaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Real scalar extension of restriction of actual group-scheme characters. -/
def rationalCharacterRestrictReal (f : H ⟶ G) :
    (ℝ ⊗[ℤ] rationalCharacters G) →ₗ[ℝ] (ℝ ⊗[ℤ] rationalCharacters H) :=
  (characterRestrict f).toIntLinearMap.baseChange ℝ

@[simp] theorem rationalCharacterRestrictReal_tmul (f : H ⟶ G) (r : ℝ)
    (χ : rationalCharacters G) :
    rationalCharacterRestrictReal f (r ⊗ₜ[ℤ] χ) = r ⊗ₜ[ℤ] characterRestrict f χ := rfl

section FullAction

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The actual quotient `N(k)/Z(k)` acts on the full integral character lattice. -/
def relativeWeylLatticeAction :
    relativeWeylGroup i →* (characterLattice T ≃ₗ[ℤ] characterLattice T) :=
  relativeWeylCharacterAction i

@[simp] theorem relativeWeylLatticeAction_mk (n : normalizerPoints i) :
    relativeWeylLatticeAction i (QuotientGroup.mk n) = weylAction i n := rfl

/-- Rational scalar extension of the full integral relative Weyl action. -/
def relativeWeylFullRatAction :
    relativeWeylGroup i →* ((ℚ ⊗[ℤ] characterLattice T) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] characterLattice T)) :=
  ratAut.comp (relativeWeylLatticeAction i)

@[simp] theorem relativeWeylFullRatAction_tmul (w : relativeWeylGroup i)
    (q : ℚ) (χ : characterLattice T) :
    relativeWeylFullRatAction i w (q ⊗ₜ[ℤ] χ) =
      q ⊗ₜ[ℤ] relativeWeylLatticeAction i w χ := rfl

@[simp] theorem relativeWeylFullRatAction_mk (n : normalizerPoints i) :
    relativeWeylFullRatAction i (QuotientGroup.mk n) = ratAut (weylAction i n) := rfl

/-- Real scalar extension of the full integral action on the published `Vstar T`. -/
def relativeWeylFullRealAction :
    relativeWeylGroup i →* (RealTorusSpace.Vstar T ≃ₗ[ℝ] RealTorusSpace.Vstar T) where
  toFun w := LinearEquiv.baseChange ℤ ℝ _ _ (relativeWeylLatticeAction i w)
  map_one' := by simp
  map_mul' w z := by simp [LinearEquiv.baseChange_mul]

@[simp] theorem relativeWeylFullRealAction_tmul (w : relativeWeylGroup i)
    (r : ℝ) (χ : characterLattice T) :
    relativeWeylFullRealAction i w (r ⊗ₜ[ℤ] χ) =
      r ⊗ₜ[ℤ] relativeWeylLatticeAction i w χ := rfl

@[simp] theorem relativeWeylFullRealAction_mk (n : normalizerPoints i) :
    relativeWeylFullRealAction i (QuotientGroup.mk n) =
      RealTorusSpace.characterRealAut (normalizingAut i n) := rfl

/-- Compatibility of the full real character action with the existing real
cocharacter action, through the existing actual lattice pairing. -/
theorem pair_relativeWeyl (w : relativeWeylGroup i)
    (x : RealTorusSpace.Vstar T) (v : RealTorusSpace.V T) :
    RealTorusSpace.pair T (relativeWeylFullRealAction i w x)
      (RealTorusSpace.relativeWeylRealAction i w v) = RealTorusSpace.pair T x v := by
  refine Quotient.inductionOn w ?_
  intro n
  exact RealTorusSpace.pair_aut (normalizingAut i n) x v

variable [IsAffineHom G.X.hom]

/-- Restricting the full rational action to the actual root span recovers the
published `relativeWeylAction`, for every quotient class. -/
theorem coe_relativeWeylAction_apply (w : relativeWeylGroup i) (x : relativeRootSpan i) :
    (relativeWeylAction i w x : ℚ ⊗[ℤ] characterLattice T) =
      relativeWeylFullRatAction i w x := by
  refine Quotient.inductionOn w ?_
  intro n
  rfl

/-- The full lattice action preserves all actual relative roots. -/
theorem relativeWeylLatticeAction_mapsTo_relativeRoots (w : relativeWeylGroup i) :
    Set.MapsTo (relativeWeylLatticeAction i w) (relativeRoots i) (relativeRoots i) := by
  refine Quotient.inductionOn w ?_
  intro n
  exact weylAction_mapsTo_relativeRoots i n

end FullAction

namespace RealTorusSpace

variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Postcomposition on the actual integral cocharacter lattices. -/
def cocharacterMapInt (f : A ⟶ T) : cocharacterLattice A →ₗ[ℤ] cocharacterLattice T :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun ν => ν ≫ f
      map_zero' := by simp
      map_add' := fun ν μ => Preadditive.add_comp _ _ _ _ _ _ }

/-- Real scalar extension of postcomposition on actual cocharacters. -/
def cocharacterMapReal (f : A ⟶ T) : V A →ₗ[ℝ] V T :=
  (cocharacterMapInt f).baseChange ℝ

@[simp] theorem cocharacterMapReal_tmul (f : A ⟶ T) (r : ℝ)
    (ν : cocharacterLattice A) :
    cocharacterMapReal f (r ⊗ₜ[ℤ] ν) = r ⊗ₜ[ℤ] (ν ≫ f) := rfl

/-- The simultaneous annihilator of specified actual characters in the
published real cocharacter space. -/
def rootAnnihilator (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (R : Set (characterLattice T)) : Submodule ℝ (V T) :=
  ⨅ (α : characterLattice T) (_ : α ∈ R), (eval T α).ker

@[simp] theorem mem_rootAnnihilator (R : Set (characterLattice T)) (v : V T) :
    v ∈ rootAnnihilator T R ↔ ∀ α ∈ R, eval T α v = 0 := by
  simp only [rootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]

@[simp] theorem rootAnnihilator_empty :
    rootAnnihilator T ∅ = ⊤ := by
  ext v
  simp

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- The simultaneous annihilator of all actual relative roots. Its geometric
identification with the split center is a separate structural proposition. -/
def relativeCentralDirections : Submodule ℝ (V T) :=
  rootAnnihilator T (relativeRoots i)

@[simp] theorem mem_relativeCentralDirections (v : V T) :
    v ∈ relativeCentralDirections i ↔ ∀ α ∈ relativeRoots i, eval T α v = 0 :=
  mem_rootAnnihilator _ _

/-- The real span of the actual integral relative roots in the full published
real character space, retaining the full central complement. -/
def relativeRootSpanReal : Submodule ℝ (Vstar T) :=
  Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' relativeRoots i)

/-- Root annihilation is preserved by the existing actual relative Weyl
cocharacter action. Pointwise fixedness is a separate structural assertion. -/
theorem relativeWeylRealAction_mem_relativeCentralDirections [Mono i.hom.hom.left]
    (w : relativeWeylGroup i) {v : V T} (hv : v ∈ relativeCentralDirections i) :
    relativeWeylRealAction i w v ∈ relativeCentralDirections i := by
  refine Quotient.inductionOn w ?_
  intro n
  rw [mem_relativeCentralDirections] at hv ⊢
  intro α hα
  change eval T α (n • v) = 0
  rw [eval_normalizer_smul]
  exact hv _ (weylAction_mapsTo_relativeRoots i n⁻¹ hα)

end RealTorusSpace

end Langlands.GroupScheme
