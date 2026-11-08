import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation
import Langlands.Geometry.Building.AdditiveRootCoordinateValuation

/-! # The Chevalley root function family of a Chevalley group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.SplitExistence
open Langlands.GroupScheme.SplitExistence.ChevalleyData

namespace Langlands.Geometry.Building

namespace ChevalleyRootFamily

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  {D : ChevalleyData P b} {k : Type u} [Field k]

/-- The rational points of `𝔾ₐ` attached to a field element are scalar points. -/
theorem gaRationalEquiv_eq_scalarPoint (x : k) :
    gaRationalEquiv k (Multiplicative.ofAdd x) =
      VectorGroup.scalarPoint (CommRingCat.of k) (Over.mk (𝟙 (Spec (CommRingCat.of k))))
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv x) := by
  apply VectorGroup.points_ext
  intro i
  fin_cases i
  rw [VectorGroup.coordinates_scalarPoint]
  exact gaCoord_gaRationalEquiv k (Multiplicative.ofAdd x)

/-- On base points, the global value of a character is its rational value. -/
theorem charValue_eq_rationalCharacterEval {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice T) (z : rationalPoints T.toGrp) :
    VectorGroup.charValue χ (Over.mk (𝟙 (Spec (CommRingCat.of k)))) z =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice T).symm χ) z : k) := by
  rw [rationalCharacterEval_apply, Gm.affinePointsEquiv_val]
  change _ = ((Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ (Scheme.ΓSpecIso _).inv) _
  rw [Iso.hom_inv_id]
  rfl

variable (G : D.ChevGroup k) [Finite J] [P.IsReduced] [Module.Finite ℤ X] [Module.Free ℤ X]
  [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom]

/-- The field coordinates of a root group, as an equivalence onto `rootGroupPoints`. -/
def rootCoord (j : J) : Multiplicative k ≃* rootGroupPoints G.t (charOf k (P.root j)) :=
  G.rootCoordEquiv j

theorem rootCoord_apply_coe (j : J) (s : Multiplicative k) :
    (rootCoord G j s : rationalPoints G.H) = gaRationalEquiv k s ≫ (G.u j).hom.hom :=
  rfl

/-- Root-group coordinates for any character equal to a root character. -/
def coordOfEq {a : characterLattice (Tk (X := X) k)} {j : J} (h : charOf k (P.root j) = a) :
    Multiplicative k ≃* rootGroupPoints G.t a :=
  (rootCoord G j).trans (MulEquiv.subgroupCongr (congrArg (rootGroupPoints G.t) h))

variable (omega : AddValuation k (WithTop ℝ))

/-- The Chevalley root function family: on the root group of a root it is the valuation of
the root coordinate, and it is infinite elsewhere. -/
def family : RootFunctionFamily (Tk (X := X) k) G.H where
  toFun a g := by
    classical
    exact if h : ∃ j, charOf k (P.root j) = a then
      additiveRootValue omega (coordOfEq G h.choose_spec) g else ⊤

omit [Finite J] [P.IsReduced] [IsAffine G.H.X.left] [LocallyOfFiniteType G.H.X.hom] in
/-- Root characters of distinct roots are distinct. -/
theorem charOf_root_injective :
    Function.Injective fun j : J => charOf k (P.root j) := by
  intro j j' h
  apply P.root.injective
  apply (charEquiv k (X := X)).injective
  rw [charEquiv_apply, charEquiv_apply]
  exact h

/-- On a root character the family is the coordinate valuation. -/
theorem family_root (j : J) (g : rationalPoints G.H) :
    family G omega (charOf k (P.root j)) g = additiveRootValue omega (rootCoord G j) g := by
  classical
  have h : ∃ j', charOf k (P.root j') = charOf k (P.root j) := ⟨j, rfl⟩
  change (if h : ∃ j', charOf k (P.root j') = charOf k (P.root j) then
    additiveRootValue omega (coordOfEq G h.choose_spec) g else ⊤) = _
  rw [dite_eq_left_of_eq_true (eq_true h)]
  have hj : h.choose = j := charOf_root_injective h.choose_spec
  have key : ∀ (j' : J) (hj' : charOf k (P.root j') = charOf k (P.root j)), j' = j →
      additiveRootValue omega (coordOfEq G hj') g =
        additiveRootValue omega (rootCoord G j) g := by
    rintro j' hj' rfl
    rfl
  exact key _ _ hj

/-- Off the root characters the family is infinite. -/
theorem family_of_not_root {a : characterLattice (Tk (X := X) k)}
    (ha : ∀ j, charOf k (P.root j) ≠ a) (g : rationalPoints G.H) :
    family G omega a g = ⊤ := by
  classical
  change (if h : ∃ j, charOf k (P.root j) = a then
    additiveRootValue omega (coordOfEq G h.choose_spec) g else ⊤) = ⊤
  rw [dite_eq_right_of_eq_false (eq_false fun ⟨j, hj⟩ => ha j hj)]

/-- The relative roots of the torus of a Chevalley group are the root characters. -/
theorem mem_relativeRoots_iff (a : characterLattice (Tk (X := X) k)) :
    a ∈ relativeRoots G.t ↔ ∃ j, charOf k (P.root j) = a := by
  rw [relativeRoots, G.roots_t]
  rfl

theorem eq_top_of_not_mem_roots :
    ∀ a ∉ relativeRoots G.t, ∀ g, family G omega a g = ⊤ := by
  intro a ha g
  apply family_of_not_root
  intro j hj
  exact ha ((mem_relativeRoots_iff G a).2 ⟨j, hj⟩)

theorem eq_top_of_not_mem :
    ∀ a ∈ relativeRoots G.t, ∀ g ∉ rootGroupPoints G.t a, family G omega a g = ⊤ := by
  intro a ha g hg
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  rw [family_root]
  exact additiveRootValue_of_not_mem omega _ hg

theorem one_mem :
    ∀ a ∈ relativeRoots G.t, ∀ r : ℝ, (1 : rationalPoints G.H) ∈ rootFiltration G.t (family G omega) a r := by
  intro a ha r
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  refine ⟨(rootGroupPoints G.t _).one_mem, ?_⟩
  rw [family_root, additiveRootValue_one]
  exact le_top

theorem mul_mem :
    ∀ a ∈ relativeRoots G.t, ∀ r : ℝ, ∀ g h : rationalPoints G.H,
      g ∈ rootFiltration G.t (family G omega) a r → h ∈ rootFiltration G.t (family G omega) a r →
        g * h ∈ rootFiltration G.t (family G omega) a r := by
  intro a ha r g h hg hh
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  refine ⟨(rootGroupPoints G.t _).mul_mem hg.1 hh.1, ?_⟩
  have hg2 := hg.2
  have hh2 := hh.2
  rw [family_root] at hg2 hh2 ⊢
  exact (le_min hg2 hh2).trans (additiveRootValue_mul_ge omega _ hg.1 hh.1)

theorem inv_mem :
    ∀ a ∈ relativeRoots G.t, ∀ r : ℝ, ∀ g : rationalPoints G.H,
      g ∈ rootFiltration G.t (family G omega) a r → g⁻¹ ∈ rootFiltration G.t (family G omega) a r := by
  intro a ha r g hg
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  refine ⟨(rootGroupPoints G.t _).inv_mem hg.1, ?_⟩
  have hg2 := hg.2
  rw [family_root] at hg2 ⊢
  rw [additiveRootValue_inv omega _ hg.1]
  exact hg2

theorem eq_top_iff :
    ∀ a ∈ relativeRoots G.t, ∀ g ∈ rootGroupPoints G.t a, family G omega a g = ⊤ ↔ g = 1 := by
  intro a ha g hg
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  rw [family_root]
  exact additiveRootValue_eq_top_iff omega _ hg

theorem three_le_encard (hω : 3 ≤ (Set.range omega).encard) :
    ∀ a ∈ relativeRoots G.t, 3 ≤ (family G omega a '' rootGroupPoints G.t a).encard := by
  intro a ha
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  refine hω.trans (Set.encard_le_encard ?_)
  rintro _ ⟨x, rfl⟩
  refine ⟨rootCoord G j (Multiplicative.ofAdd x),
    (rootCoord G j (Multiplicative.ofAdd x)).property, ?_⟩
  rw [family_root, additiveRootValue_coordinate]

/-- Axiom V 4 holds vacuously: no root of a Chevalley group of a reduced root datum is
twice a root. -/
theorem double :
    ∀ a ∈ relativeRoots G.t, 2 • a ∈ relativeRoots G.t →
      ∀ u ∈ rootGroupPoints G.t (2 • a), family G omega (2 • a) u = 2 • family G omega a u := by
  intro a ha h2
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  exact absurd h2 (G.hasNoHigherRoots_charOf j 2 le_rfl)

/-- Rational torus conjugation of root points multiplies the coordinate by the root value. -/
theorem conj_rootCoordEquiv (j : J) (s : rationalPoints (Tk (X := X) k).toGrp) (x : k) :
    (rationalPoints.map G.t s)⁻¹ * (rootCoord G j (Multiplicative.ofAdd x) : rationalPoints G.H) *
        ((rationalPoints.map G.t s)⁻¹)⁻¹ =
      (rootCoord G j (Multiplicative.ofAdd
        (((rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm
          (charOf k (P.root j))) s)⁻¹ : kˣ) * x)) : rationalPoints G.H) := by
  rw [rootCoord_apply_coe, rootCoord_apply_coe,
    gaRationalEquiv_eq_scalarPoint, gaRationalEquiv_eq_scalarPoint, ← map_inv,
    rationalPoints.map_apply]
  rw [(G.u_isTorusEquivariant j) _ s⁻¹]
  congr 2
  rw [charValue_eq_rationalCharacterEval, map_inv, map_mul]

/-- Split-torus compatibility of the Chevalley root family. -/
theorem isSplitTorusCompatible (ω : kˣ → ℝ) (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ)) :
    IsSplitTorusCompatible G.t ω (family G omega) := by
  intro a ha s u hu
  obtain ⟨j, rfl⟩ := (mem_relativeRoots_iff G a).1 ha
  rw [family_root, family_root]
  set c := rationalCharacterEval ((rationalCharacters.equivCharacterLattice _).symm
    (charOf k (P.root j))) s
  have h := additiveRootValue_conjugation_of_scalar omega (rootCoord G j)
    (rationalPoints.map G.t s)⁻¹ ((c⁻¹ : kˣ) : k) (fun x => conj_rootCoordEquiv G j s x) hu
  rw [inv_inv] at h
  rw [h, hω]
  congr 1
  have h1 : omega ((c⁻¹ : kˣ) : k) + omega (c : k) = 0 := by
    rw [← omega.map_mul, Units.inv_mul, omega.map_one]
  rw [hω, hω] at h1
  have h2 : ω c⁻¹ + ω c = 0 := by exact_mod_cast h1
  rw [WithTop.coe_eq_coe]
  linarith

end ChevalleyRootFamily

end Langlands.Geometry.Building
