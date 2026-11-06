import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Orbit-dimension strata of unipotent actions and their quotient spaces

Conrad's Example 5.5. Let `G` be a unipotent algebraic group over a henselian valued
field `k` of characteristic zero acting on a reduced `k`-scheme `V` of finite type. The
points of `V` whose orbit has dimension `d` form a locally closed set `V_d`. On the
reduced subscheme `V_d` the action restricts, the stabilizer scheme over `V_d` is flat,
and the fppf sheaf quotient `V_d/G` is a finitely presented algebraic space receiving a
faithfully flat map from `V_d`. Its rational points are locally Hausdorff, locally compact
when `k` is locally compact and locally totally disconnected when `k` is non-archimedean.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction IsUnipotent)
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A transformation of presheaves on schemes over `S` is flat when it is representable by
actual schemes and every represented projection is a flat scheme morphism. -/
def IsFlat {S : Scheme.{u}} {F G : Presheaf S} (f : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Flat.{u}) (Over.forget S)).relative (schemeYoneda S) f

variable {S : Scheme.{u}} {G : GroupScheme S} {V : Over S}

/-- The stabilizer of an action `a` of `G` on `V`, as a scheme over `V` along this
projection: the base change of the action graph `G × V → V × V`, `(g, v) ↦ (g.v, v)`,
along the diagonal of `V`. It is flat when the graph is flat over the diagonal. -/
def IsStabilizerFlat (a : SchemeAction G V) : Prop :=
  Flat (pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))).left

/-- The orbit of a point `v` of `V` has dimension `d`: the dimension of `G` equals
`d` plus the dimension of the stabilizer of `v`, the fibre over `v` of the stabilizer
scheme. -/
def HasOrbitDimension (a : SchemeAction G V) (v : V.left) (d : ℕ) : Prop :=
  let σ := pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V))
  topologicalKrullDim G.X.left = topologicalKrullDim (σ.left.fiber v) + (d : WithBot ℕ∞)

/-- The fppf sheaf quotient of `V` by the action `a`: the map `π` from the sheaf of `V`
coequalizes the action and the projection `G × V ⇉ V` in fppf sheaves. -/
def IsFppfActionQuotient (a : SchemeAction G V) {Q : FppfSheaf S}
    (π : (schemeSheaf S).obj V ⟶ Q) : Prop :=
  ∃ w : (schemeSheaf S).map a.hom ≫ π = (schemeSheaf S).map (snd G.X V) ≫ π,
    Nonempty (IsColimit (Cofork.ofπ π w))

variable (K : Type u) [NontriviallyNormedField K]

/-- Conrad's unipotent algebraic groups over `K`: affine group schemes locally of finite
type over `Spec K` that are unipotent. -/
def IsUnipotentAlgebraicGroup (G : GroupScheme (Spec (CommRingCat.of K))) : Prop :=
  IsAffineHom G.X.hom ∧ LocallyOfFiniteType G.X.hom ∧ IsUnipotent G

/-- The source's reduced `K`-schemes of finite type. -/
def IsReducedFiniteType (V : Over (Spec (CommRingCat.of K))) : Prop :=
  IsReduced V.left ∧ LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom

/-- The rational points of `X` are locally Hausdorff, locally compact when `K` is, and
locally totally disconnected when `K` is non-archimedean: every point has an open
neighbourhood that is Hausdorff, locally compact if `K` is, and totally disconnected if
the norm of `K` is ultrametric. -/
def HasLocallyHausdorffRationalPoints (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    Prop :=
  letI : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  ∀ x : RingPoints K X K, ∃ W : Set (RingPoints K X K), IsOpen W ∧ x ∈ W ∧
    T2Space W ∧ (LocallyCompactSpace K → LocallyCompactSpace W) ∧
    (IsUltrametricDist K → TotallyDisconnectedSpace W)

/-- Conrad's Example 5.5 (printed p.16), the orbit-dimension strata: for a unipotent
algebraic group `G` over a henselian valued field `K` of characteristic zero acting on a
reduced `K`-scheme `V` of finite type, the set of points of `V` whose orbit has dimension
`d` is locally closed. -/
def UnipotentOrbitStratumLocallyClosedStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K → CharZero K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))), IsUnipotentAlgebraicGroup K G →
    ∀ (V : Over (Spec (CommRingCat.of K))), IsReducedFiniteType K V →
    ∀ (a : SchemeAction G V) (d : ℕ), IsLocallyClosed {v : V.left | HasOrbitDimension a v d}

/-- Conrad's Example 5.5 (printed p.16), the quotient `V_d/G`: in the setting of
`UnipotentOrbitStratumLocallyClosedStatement`, let `i : Z → V` be an immersion from a
reduced scheme onto the points with orbit dimension `d`. The action restricts to an
action `b` on `Z` making `i` equivariant, the stabilizer of `b` is flat over `Z`, and the
fppf sheaf quotient of `Z` by `b` is a quasi-separated algebraic space of finite
presentation over `Spec K`, receiving a flat surjective quotient map from `Z`. -/
def UnipotentOrbitStratumQuotientStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K → CharZero K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))), IsUnipotentAlgebraicGroup K G →
    ∀ (V : Over (Spec (CommRingCat.of K))), IsReducedFiniteType K V →
    ∀ (a : SchemeAction G V) (d : ℕ) (Z : Over (Spec (CommRingCat.of K))) (i : Z ⟶ V),
      IsImmersion i.left → IsReduced Z.left →
      Set.range i.left.base = {v : V.left | HasOrbitDimension a v d} →
      ∃ b : SchemeAction G Z, b.hom ≫ i = (G.X ◁ i) ≫ a.hom ∧ IsStabilizerFlat b ∧
        ∃ (X : AlgebraicSpace (Spec (CommRingCat.of K)))
          (π : (schemeSheaf _).obj Z ⟶ X.toSheaf),
          IsFppfActionQuotient b π ∧ IsQuasiSeparated X ∧ FinitePresentationOverRing K X ∧
            IsFlat π.hom ∧ IsSurjective π.hom

/-- Conrad's Example 5.5 (printed p.16), the topology on `(V_d/G)(K)`, with the source's
local compactness and local total disconnectedness qualified by the corresponding
properties of `K`: in the setting of `UnipotentOrbitStratumQuotientStatement`, every
algebraic space `X` that is an fppf sheaf quotient of `Z` by an action `b` making `i`
equivariant has locally Hausdorff rational points, locally compact when `K` is locally
compact and locally totally disconnected when `K` is non-archimedean. -/
def UnipotentOrbitQuotientPointTopologyStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K → CharZero K →
    ∀ (G : GroupScheme (Spec (CommRingCat.of K))), IsUnipotentAlgebraicGroup K G →
    ∀ (V : Over (Spec (CommRingCat.of K))), IsReducedFiniteType K V →
    ∀ (a : SchemeAction G V) (d : ℕ) (Z : Over (Spec (CommRingCat.of K))) (i : Z ⟶ V),
      IsImmersion i.left → IsReduced Z.left →
      Set.range i.left.base = {v : V.left | HasOrbitDimension a v d} →
      ∀ (b : SchemeAction G Z), b.hom ≫ i = (G.X ◁ i) ≫ a.hom →
      ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K)))
        (π : (schemeSheaf _).obj Z ⟶ X.toSheaf), IsFppfActionQuotient b π →
        HasLocallyHausdorffRationalPoints K X

/-- Conrad's Example 5.5 (printed p.16): the conjunction of
`UnipotentOrbitStratumLocallyClosedStatement`, `UnipotentOrbitStratumQuotientStatement`
and `UnipotentOrbitQuotientPointTopologyStatement`. -/
def UnipotentOrbitQuotientStatement : Prop :=
  UnipotentOrbitStratumLocallyClosedStatement.{u} ∧ UnipotentOrbitStratumQuotientStatement.{u} ∧
    UnipotentOrbitQuotientPointTopologyStatement.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace
