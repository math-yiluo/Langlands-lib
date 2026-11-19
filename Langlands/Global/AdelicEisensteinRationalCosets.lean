import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicParabolicQuotient
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Rational coset evaluation of adelic Eisenstein terms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Opposite NumberField Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {iU : U ⟶ P} {l : M ⟶ P}

/-- The rational points of the parabolic map into the inducing subgroup. -/
theorem map_rational_mem_parabolicQuotientSubgroup (hl : IsRationalLeviSubgroup l)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) (q : RationalGroupPoints F P) :
    map F P G p (rational F P q) ∈ parabolicQuotientSubgroup F p iU l := by
  obtain ⟨U', j, hj, hmul⟩ := hl.exists_unipotentRadical
  let := hmul
  let T := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F))
  let z : T ⟶ M.X ⊗ U'.X := q ≫ inv (subgroupMultiplication l j)
  let m : RationalGroupPoints F M := z ≫ fst M.X U'.X
  have hn : (z ≫ snd M.X U'.X) ≫ j.hom.hom ∈ (SubgroupFunctor.range iU).carrier T :=
    hU.1.greatest U' j hj.1.isClosedSubgroup hj.1.smooth hj.1.connectedSpace
      hj.1.isUnipotent hj.1.isNormal T ⟨z ≫ snd M.X U'.X, rfl⟩
  obtain ⟨n, hn⟩ := hn
  change RationalGroupPoints F U at n
  change n ≫ iU.hom.hom = (z ≫ snd M.X U'.X) ≫ j.hom.hom at hn
  have hz : lift (z ≫ fst M.X U'.X) (z ≫ snd M.X U'.X) = z := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hq : M.affinePointsTarget l (CommAlgCat.of F F) m *
      U.affinePointsTarget iU (CommAlgCat.of F F) n = q := by
    change (m ≫ l.hom.hom) * (n ≫ iU.hom.hom) = q
    have hcomp := comp_subgroupMultiplication l j (z ≫ fst M.X U'.X) (z ≫ snd M.X U'.X)
    rw [hz] at hcomp
    rw [hn, ← hcomp]
    simp [z]
  have hr (H : GroupScheme (Spec (CommRingCat.of F))) (f : H ⟶ P)
      (x : RationalGroupPoints F H) :
      map F P G p (rational F P (H.affinePointsTarget f (CommAlgCat.of F F) x)) =
        map F H G (f ≫ p) (rational F H x) := by
    rw [map_comp_apply_of_hom]
    exact congrArg (map F P G p) (DFunLike.congr_fun (rational_naturality F H f) x)
  rw [← hq, map_mul, map_mul, hr M l m, hr U iU n]
  exact mul_mem (Subgroup.mem_sup_right ⟨m, rfl⟩)
    (Subgroup.mem_sup_left ⟨rational F U n, rfl⟩)

variable [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  {φ : AdelicGroupPoints F G → ℂ}

/-- The twist is invariant under rational points of the parabolic. -/
theorem IsIwasawaCompact.parameterTwist_rational_mul (hK : IsIwasawaCompact p K)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (q : RationalGroupPoints F P)
    (g : AdelicGroupPoints F G) :
    hK.parameterTwist φ lam (map F P G p (rational F P q) * g) =
      hK.parameterTwist φ lam g := by
  rw [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.parameterTwist,
    hφ _ (map_rational_mem_parabolicQuotientSubgroup hl hU q) g,
    IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, hK.height_rational_mul]

/-- Evaluate the twist by descent from rational points to their parabolic right cosets. -/
def IsIwasawaCompact.parameterTwistOnCosets (hK : IsIwasawaCompact p K)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    ParabolicRationalCosets F p → ℂ :=
  Quotient.lift (fun x : rationalSubgroup F G => hK.parameterTwist φ lam (x.val * g)) (by
    intro x y h
    have hyx := (QuotientGroup.rightRel_apply).mp h
    change (y : AdelicGroupPoints F G) * (x : AdelicGroupPoints F G)⁻¹ ∈
      (rationalSubgroup F P).map (map F P G p).toMonoidHom at hyx
    obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hyx
    change map F P G p (rational F P q) =
      (y : AdelicGroupPoints F G) * (x : AdelicGroupPoints F G)⁻¹ at hq
    have hmul : (y : AdelicGroupPoints F G) * g =
        map F P G p (rational F P q) * (x.val * g) := by rw [hq]; group
    rw [hmul, hK.parameterTwist_rational_mul hφ hl hU])

/-- A rational point in a given coset computes the published Eisenstein term. -/
theorem IsIwasawaCompact.eisensteinTerm_eq_of_representative (hK : IsIwasawaCompact p K)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (c : ParabolicRationalCosets F p) (x : rationalSubgroup F G)
    (hx : Quotient.mk _ x = c) :
    hK.eisensteinTerm φ lam g c = hK.parameterTwist φ lam (x.val * g) := by
  calc
    _ = hK.parameterTwistOnCosets hφ hl hU lam g (Quotient.mk _ (Quotient.out c)) := rfl
    _ = hK.parameterTwistOnCosets hφ hl hU lam g (Quotient.mk _ x) := by
      rw [Quotient.out_eq, hx]
    _ = _ := rfl

end Langlands.Global.AdelicGroupPoints
