import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Rational.TorusTransporterOrbit

/-! # Galois differences of transporters between descended tori -/

set_option maxHeartbeats 800000

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme

namespace StarActionIndependence

/-- Conjugating-point membership respects equality of the point. -/
theorem IsConjugatingPoint.of_point_eq
    {B : Scheme.{u}} {T T' : CommGroupScheme B} {G : GroupScheme B}
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
    {n m : Over.mk (𝟙 B) ⟶ G.X} {e : T ≅ T'}
    (hn : IsConjugatingPoint i j n e) (hm : m = n) :
    IsConjugatingPoint i j m e := by
  cases hm
  exact hn

/-- Canonical descent transports a conjugating point identified by an equality. -/
theorem IsConjugatingPoint.baseChange_descent_of_eq
    {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    {T T' : CommGroupScheme B} {G : GroupScheme B}
    (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
    {n m : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X}
    {e : (CommGroupScheme.baseChange b).obj T ≅ (CommGroupScheme.baseChange b).obj T'}
    (hn : IsConjugatingPoint (C := (CommGroupScheme.baseChange b).obj T)
      (C' := (CommGroupScheme.baseChange b).obj T')
      ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j) n e)
    (hm : m = Langlands.GroupScheme.baseChangeBasePoint a ((GroupScheme.baseChange b).obj G) n ≫
      (descentBaseChangeIso b a ha G).hom.hom.hom) :
    IsConjugatingPoint (C := (CommGroupScheme.baseChange b).obj T)
      (C' := (CommGroupScheme.baseChange b).obj T')
      ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map j) m
      ((CommGroupScheme.descentBaseChangeIso b a ha T).symm ≪≫
        (CommGroupScheme.baseChange a).mapIso e ≪≫
          CommGroupScheme.descentBaseChangeIso b a ha T') :=
  (hn.baseChange_descent b a ha i j).of_point_eq hm

end StarActionIndependence

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "T'_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T'
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

/-- A transporter between two embedded commutative groups defined over `k`
has normalizer-valued coefficient differences over any field extension. -/
theorem inv_mul_rationalConjugate_mem_normalizerPoints_of_transporters
    (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G) (σ : K ≃ₐ[k] K)
    {g : rationalPoints G_K} {e : T_K ≅ T'_K}
    (hg : i_K i ≫ ((G_K).innerIso g).hom =
      CommGroupScheme.groupHom e.hom ≫ i_K j) :
    g⁻¹ * rationalConjugate k K G σ g ∈ normalizerPoints (T := T_K) (i_K i) := by
  have h : StarActionIndependence.IsConjugatingPoint
      (C := T_K) (C' := T'_K) (i_K i) (i_K j) g e := hg
  have hσ := h.baseChange_descent_of_eq b (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) i j
    (rationalConjugate_eq_baseChange_descent k K σ g)
  exact inv_mul_mem_normalizerPoints_of_transporters hσ hg

end Langlands.GroupScheme
