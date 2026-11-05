import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointStatement
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# The topology on rational points of algebraic spaces over henselian fields

Conrad's Proposition 5.4: over a henselian valued field there is a unique family
of topologies on the rational points of quasi-separated locally finite type
algebraic spaces that is functorial, agrees with the scheme topology, is compatible
with fibre products, and carries open immersions, closed immersions and étale maps
to open embeddings, closed embeddings and local homeomorphisms. For separated
spaces it is Hausdorff, totally disconnected over non-archimedean fields and
locally compact over locally compact fields.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Étale morphisms of algebraic spaces, in the Stacks Project sense (Tag 03FR): the
composite with every étale map from an actual scheme is étale. The source need not be
representable over the target. -/
def IsEtaleMorphism {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (U : Over S) (φ : (schemeYoneda S).obj U ⟶ X.presheaf), IsEtale φ → IsEtale (φ ≫ hom f)

variable (K : Type u) [NontriviallyNormedField K]

/-- The spaces of Conrad's Proposition 5.4: quasi-separated and locally of finite
type over `Spec K`. -/
def IsQuasiSeparatedLocallyFiniteType
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) : Prop :=
  IsQuasiSeparated X ∧ LocallyOfFiniteTypeOverBase X

/-- The properties of Conrad's Proposition 5.4 for a family `τ` of topologies on
rational points, required for all quasi-separated locally finite type spaces. -/
def IsAdmissibleRationalPointTopology
    (τ : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
      TopologicalSpace (RingPoints K X K)) : Prop :=
  -- functoriality
  (∀ ⦃X Y : AlgebraicSpace (Spec (CommRingCat.of K))⦄ (f : X ⟶ Y),
    IsQuasiSeparatedLocallyFiniteType K X → IsQuasiSeparatedLocallyFiniteType K Y →
      @Continuous _ _ (τ X) (τ Y) (RingPoints.map (A := K) f)) ∧
  -- the case of schemes
  (∀ (U : Over (Spec (CommRingCat.of K))),
    IsQuasiSeparatedLocallyFiniteType K ((schemeToSpace _).obj U) →
      @IsHomeomorph _ _ (τ ((schemeToSpace _).obj U)) (schemePointTopology K U K)
        (schemeRingPointsEquiv K U K)) ∧
  -- fibre products
  (∀ ⦃P X' X'' X : AlgebraicSpace (Spec (CommRingCat.of K))⦄
    (p' : P ⟶ X') (p'' : P ⟶ X'') (f' : X' ⟶ X) (f'' : X'' ⟶ X),
    IsQuasiSeparatedLocallyFiniteType K P → IsQuasiSeparatedLocallyFiniteType K X' →
    IsQuasiSeparatedLocallyFiniteType K X'' → IsQuasiSeparatedLocallyFiniteType K X →
    IsPullback (hom p') (hom p'') (hom f') (hom f'') →
      @Topology.IsEmbedding _ _ (τ P) (@instTopologicalSpaceProd _ _ (τ X') (τ X''))
        (fun w : RingPoints K P K => (RingPoints.map p' w, RingPoints.map p'' w))) ∧
  -- open immersions
  (∀ ⦃X' X : AlgebraicSpace (Spec (CommRingCat.of K))⦄ (f : X' ⟶ X),
    IsQuasiSeparatedLocallyFiniteType K X' → IsQuasiSeparatedLocallyFiniteType K X →
    IsOpenImmersion (hom f) →
      @Topology.IsOpenEmbedding _ _ (τ X') (τ X) (RingPoints.map (A := K) f)) ∧
  -- closed immersions
  (∀ ⦃X' X : AlgebraicSpace (Spec (CommRingCat.of K))⦄ (f : X' ⟶ X),
    IsQuasiSeparatedLocallyFiniteType K X' → IsQuasiSeparatedLocallyFiniteType K X →
    IsClosedImmersion (hom f) →
      @Topology.IsClosedEmbedding _ _ (τ X') (τ X) (RingPoints.map (A := K) f)) ∧
  -- étale maps
  (∀ ⦃X' X : AlgebraicSpace (Spec (CommRingCat.of K))⦄ (f : X' ⟶ X),
    IsQuasiSeparatedLocallyFiniteType K X' → IsQuasiSeparatedLocallyFiniteType K X →
    IsEtaleMorphism f →
      @IsLocalHomeomorph _ _ (τ X') (τ X) (RingPoints.map (A := K) f))

/-- The separated-space properties of Conrad's Proposition 5.4 for a family `τ`:
Hausdorff, totally disconnected over a non-archimedean field, and locally compact
over a locally compact field. -/
def SeparatedRationalPointTopologyProperties
    (τ : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
      TopologicalSpace (RingPoints K X K)) : Prop :=
  ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
    IsQuasiSeparatedLocallyFiniteType K X → IsSeparated X →
      @T2Space _ (τ X) ∧
      (IsUltrametricDist K → @TotallyDisconnectedSpace _ (τ X)) ∧
      (LocallyCompactSpace K → @LocallyCompactSpace _ (τ X))

/-- Conrad's Proposition 5.4 (printed pp.14–15), topological part: over a henselian
valued field there is a family of topologies on rational points with the stated
properties, any two such families agree on quasi-separated locally finite type
spaces, and on separated spaces the topology is Hausdorff, totally disconnected
over non-archimedean fields and locally compact over locally compact fields. -/
def HenselianSpacePointTopologyStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∃ τ : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
        TopologicalSpace (RingPoints K X K),
      IsAdmissibleRationalPointTopology K τ ∧
      (∀ τ' : ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
          TopologicalSpace (RingPoints K X K),
        IsAdmissibleRationalPointTopology K τ' →
          ∀ X, IsQuasiSeparatedLocallyFiniteType K X → τ' X = τ X) ∧
      SeparatedRationalPointTopologyProperties K τ

end Langlands.AlgebraicGeometry.AlgebraicSpace
