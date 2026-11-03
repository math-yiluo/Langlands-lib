import Langlands.Topology.LocallyConstant.Correspondence
import Langlands.Representation.LocallyConstant.CoveringTrace

/-! # Proper-pullback and covering-trace correspondence operators -/

noncomputable section

universe uX uG uR uV

namespace Langlands.CompactAction.LocallyConstantModule.CompactSupport

open CategoryTheory Limits Topology
open Langlands.LocallyConstantCovering

variable {R : Type uR} [CommRing R] {G : Type uG}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {S X Y Z : Type uX}
  [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G S] [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousSMul G S] [ContinuousSMul G X] [ContinuousSMul G Y] [ContinuousSMul G Z]

/-- Proper pullback commutes with every original smooth coefficient map. -/
theorem smoothPullback_naturality (a : C(S, X)) (ha : IsProperMap a)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    {A B : SmoothRep.{uR, uG, uV} R G} (c : A ⟶ B) :
    (coefficientFunctor (X := X)).map c ≫ smoothPullback B a ha hea =
      smoothPullback A a ha hea ≫ (coefficientFunctor (X := S)).map c := by
  ext f
  rfl

/-- Proper pullback as a natural transformation on the full coefficient category. -/
def pullbackNatTrans (a : C(S, X)) (ha : IsProperMap a)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s) :
    coefficientFunctor (R := R) (G := G) (X := X) ⟶ coefficientFunctor (X := S) where
  app A := smoothPullback A a ha hea
  naturality {_ _} c := smoothPullback_naturality a ha hea c

/-- An actual proper/covering span acts by pullback followed by unnormalized trace. -/
def correspondence (A : SmoothRep.{uR, uG, uV} R G)
    (a : C(S, X)) (b : S → Y) [∀ y, Finite (b ⁻¹' {y})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s) :
    smoothRepresentation (X := X) A ⟶ smoothRepresentation (X := Y) A :=
  smoothPullback A a ha hea ≫ smoothTrace A b hb heb

@[simp]
theorem correspondence_apply (A : SmoothRep.{uR, uG, uV} R G)
    (a : C(S, X)) (b : S → Y) [∀ y, Finite (b ⁻¹' {y})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s)
    (f : Functions R X A) (y : Y) :
    (SmoothRep.hom (correspondence A a b ha hb hea heb) f).val y =
      fiberSum b (f.val ∘ a) y := rfl

/-- Naturality retains all smooth coefficient objects and intertwiners. -/
theorem correspondence_naturality
    (a : C(S, X)) (b : S → Y) [∀ y, Finite (b ⁻¹' {y})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s)
    {A B : SmoothRep.{uR, uG, uV} R G} (c : A ⟶ B) :
    (coefficientFunctor (X := X)).map c ≫ correspondence B a b ha hb hea heb =
      correspondence A a b ha hb hea heb ≫ (coefficientFunctor (X := Y)).map c := by
  exact (pullbackNatTrans a ha hea ≫ traceNatTrans b hb heb).naturality c

/-- The correspondence is natural in the entire original smooth coefficient category. -/
def correspondenceNatTrans
    (a : C(S, X)) (b : S → Y) [∀ y, Finite (b ⁻¹' {y})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s) :
    coefficientFunctor (R := R) (G := G) (X := X) ⟶ coefficientFunctor (X := Y) :=
  pullbackNatTrans a ha hea ≫ traceNatTrans b hb heb

@[simp]
theorem correspondenceNatTrans_app
    (a : C(S, X)) (b : S → Y) [∀ y, Finite (b ⁻¹' {y})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s)
    (A : SmoothRep.{uR, uG, uV} R G) :
    (correspondenceNatTrans a b ha hb hea heb).app A =
      correspondence A a b ha hb hea heb := rfl

/-- The actual identity span acts as the identity. -/
@[simp]
theorem correspondence_id [∀ x : X, Finite ((id : X → X) ⁻¹' {x})]
    (A : SmoothRep.{uR, uG, uV} R G) :
    correspondence A ⟨id, continuous_id⟩ id isProperMap_id isCoveringMap_id
        (fun _ _ => rfl) (fun _ _ => rfl) =
      𝟙 (smoothRepresentation (X := X) A) := by
  ext f
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact fiberSum_id f.val x

/-- A span with the same map on both sides counts that map's actual fiber;
no division by degree is used. -/
theorem correspondence_self_apply (A : SmoothRep.{uR, uG, uV} R G)
    (q : C(S, X)) [∀ x, Finite (q ⁻¹' {x})]
    (hp : IsProperMap q) (hc : IsCoveringMap q)
    (heq : ∀ (g : G) (s : S), q (g • s) = g • q s)
    (f : Functions R X A) (x : X) :
    (SmoothRep.hom (correspondence A q q hp hc heq heq) f).val x =
      Nat.card (q ⁻¹' {x}) • f.val x :=
  fiberSum_comap q f.val x

/-- The base-change law on the full compact-support smooth representations.
Properness and covering concern the actual four maps of the square. -/
theorem smoothTrace_baseChange
    (a : C(S, X)) (b : S → Y) (q : X → Z) (p : C(Y, Z))
    [∀ y, Finite (b ⁻¹' {y})] [∀ z, Finite (q ⁻¹' {z})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hq : IsCoveringMap q) (hp : IsProperMap p)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (hep : ∀ (g : G) (y : Y), p (g • y) = g • p y)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p))
    (A : SmoothRep.{uR, uG, uV} R G) :
    smoothPullback A a ha hea ≫ smoothTrace A b hb heb =
      smoothTrace A q hq heq ≫ smoothPullback A p hp hep := by
  ext f
  apply Subtype.ext
  apply LocallyConstant.ext
  intro y
  exact fiberSum_baseChange a b q p h f.val y

/-- Base change also holds on the complete smooth coefficient functors. -/
theorem traceNatTrans_baseChange
    (a : C(S, X)) (b : S → Y) (q : X → Z) (p : C(Y, Z))
    [∀ y, Finite (b ⁻¹' {y})] [∀ z, Finite (q ⁻¹' {z})]
    (ha : IsProperMap a) (hb : IsCoveringMap b)
    (hq : IsCoveringMap q) (hp : IsProperMap p)
    (hea : ∀ (g : G) (s : S), a (g • s) = g • a s)
    (heb : ∀ (g : G) (s : S), b (g • s) = g • b s)
    (heq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (hep : ∀ (g : G) (y : Y), p (g • y) = g • p y)
    (h : IsPullback (↾a) (↾b) (↾q) (↾p)) :
    pullbackNatTrans (R := R) a ha hea ≫ traceNatTrans b hb heb =
      traceNatTrans q hq heq ≫ pullbackNatTrans p hp hep := by
  apply NatTrans.ext
  funext A
  exact smoothTrace_baseChange a b q p ha hb hq hp hea heb heq hep h A

end Langlands.CompactAction.LocallyConstantModule.CompactSupport
