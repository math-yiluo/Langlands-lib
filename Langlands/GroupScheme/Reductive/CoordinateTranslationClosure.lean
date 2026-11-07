import Langlands.GroupScheme.Reductive.AffineCoordinateTranslation
import Langlands.GroupScheme.Reductive.SplitLeviGluingGeneratedDensity
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable

/-! # Closed envelopes of coordinate translation stabilizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.CoordinateTranslationClosure

open AffineCoordinates AffineCoordinateTranslation

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

omit [IsAffineHom G.X.hom] in
/-- Equality of rational evaluations is preserved on the Zariski closure of locations. -/
theorem appTop_eq_of_mem_rationalPointClosure
    (S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    {f g : Γ(G.X.left, ⊤)}
    (hfg : ∀ z ∈ S, z.left.appTop f = z.left.appTop g)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ rationalPointClosure G S) :
    x.left.appTop f = x.left.appTop g := by
  let : Subsingleton (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsReduced (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hs : rationalPointImage G S ⊆
      (G.X.left.basicOpen (f - g) : Set G.X.left)ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hm
    have hp : IsLocalRing.closedPoint k ∈ z.left ⁻¹ᵁ G.X.left.basicOpen (f - g) := hm
    rw [Scheme.preimage_basicOpen_top, map_sub, hfg z hz, sub_self,
      Scheme.basicOpen_zero] at hp
    exact hp
  have hc := closure_minimal hs (G.X.left.basicOpen (f - g)).isOpen.isClosed_compl hx
  have hp : x.left ⁻¹ᵁ G.X.left.basicOpen (f - g) = ⊥ := by
    ext y
    constructor
    · intro hy
      have he : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [he] at hy
      exact hc hy
    · exact False.elim
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_bot_iff, map_sub,
    sub_eq_zero] at hp
  exact hp

/-- Rational left translations which fix an actual affine coordinate. -/
def rationalLeftStabilizer (b : algebra G) :
    Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) where
  carrier := {h | ∀ g, pointAlgebraHom G _ (h * g) b = pointAlgebraHom G _ g b}
  one_mem' := by intro g; rw [one_mul]
  mul_mem' {h₁ h₂} hh₁ hh₂ := by
    intro g
    rw [mul_assoc, hh₁, hh₂]
  inv_mem' {h} hh := by
    intro g
    have he := hh (h⁻¹ * g)
    simpa only [mul_inv_cancel_left] using he.symm

/-- The rational coordinate stabilizer contains all rational points in its location closure. -/
theorem mem_rationalLeftStabilizer_of_mem_closure (b : algebra G)
    {h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hh : h ∈ rationalPointClosure G (rationalLeftStabilizer G b : Set _)) :
    h ∈ rationalLeftStabilizer G b := by
  intro g
  obtain ⟨a, ha⟩ := exists_comp_eq_mul_right g
  let f := pointAlgebraHom G G.X a b
  let c := pointAlgebraHom G G.X (G.constantPoint g G.X) b
  have he : h.left.appTop f = h.left.appTop c := by
    apply appTop_eq_of_mem_rationalPointClosure G _ _ hh
    intro z hz
    dsimp only [f, c]
    rw [appTop_pointAlgebraHom, appTop_pointAlgebraHom, ha, comp_constantPoint]
    exact hz g
  dsimp only [f, c] at he
  rw [appTop_pointAlgebraHom, appTop_pointAlgebraHom, ha, comp_constantPoint] at he
  exact he

variable [IsAlgClosed k] [Smooth G.X.hom]

/-- The smooth closed envelope of the rational coordinate stabilizer. -/
def leftStabilizerEnvelope (b : algebra G) : LeviGluing.RationalClosureEnvelope G
    (rationalLeftStabilizer G b) :=
  LeviGluing.rationalClosureEnvelope G (rationalLeftStabilizer G b)

/-- The closed envelope fixes the coordinate on arbitrary points of arbitrary tests. -/
theorem leftInvariant_stabilizerEnvelope (b : algebra G)
    (V : Over (Spec (CommRingCat.of k)))
    (h : V ⟶ (leftStabilizerEnvelope G b).group.X) (g : V ⟶ G.X) :
    pointAlgebraHom G V
      ((h ≫ (leftStabilizerEnvelope G b).inclusion.hom.hom) * g) b =
        pointAlgebraHom G V g b := by
  let E := leftStabilizerEnvelope G b
  let : Smooth E.group.X.hom := E.smooth
  apply leftInvariant_of_rationalPoints G E.group E.inclusion b _ V h g
  intro h₀ g₀
  have hh : h₀ ≫ E.inclusion.hom.hom ∈
      rationalPointClosure G (rationalLeftStabilizer G b : Set _) := by
    change E.inclusion.hom.hom.left (h₀.left (IsLocalRing.closedPoint k)) ∈
      closure (rationalPointImage G (rationalLeftStabilizer G b : Set _))
    rw [← E.range_eq]
    exact ⟨_, rfl⟩
  exact mem_rationalLeftStabilizer_of_mem_closure G b hh g₀

end Langlands.GroupScheme.CoordinateTranslationClosure
