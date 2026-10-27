import Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
import Langlands.Representation.Parabolic.RegroupingFactorEquivalences
import Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
import Langlands.Representation.Parabolic.ThreeBlockUniverseReduction

/-!
# Three-block associativity from ordered product regrouping

Given the ordered product regrouping proposition `OrderedProductRegrouping` for a topological
datum of a `p`-adic field, this module constructs an equivalence between the two bracketings
`(σ0 × (σ1 × σ2))` and `((σ0 × σ1) × σ2)` of a normalized three-block product, after the
entry-preserving rank cast along `Nat.add_assoc`. It applies the regrouping proposition to the
two refinements of `ThreeBlockRefinementGeometry`, identifies the inner one-block and two-block
products with the literal factors, and composes. The final theorem derives
`CommonUniverseThreeBlockAssociativity` from ordered regrouping at the canonical topological
data of every `p`-adic field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Normalized product induction commutes with transport of the total rank. -/
def normalizedProductInductionRankCastEquiv {m n : ℕ} (h : m = n) (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (((T.normalizedProductInductionFunctor B).obj σ).representation.comp
        (reindex (R := F.Carrier) (finCongr h)).toMonoidHom)
      ((T.normalizedProductInductionFunctor (B.rankCast h.symm)).obj σ).representation := by
  subst h
  exact Representation.Equiv.refl _

/-- Equal factor families have equivalent normalized products. -/
def normalizedProductInductionFamilyEqEquiv {n : ℕ} (B : BlockShape n)
    {σ σ' : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    (h : σ = σ') :
    letI := T.topology
    Representation.Equiv ((T.normalizedProductInductionFunctor B).obj σ).representation
      ((T.normalizedProductInductionFunctor B).obj σ').representation := by
  subst h
  exact Representation.Equiv.refl _

/-- The functor value of a factor family is its normalized product. -/
def normalizedProductInductionObjEquiv {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    Representation.Equiv ((T.normalizedProductInductionFunctor B).obj σ).representation
      (T.normalizedProductInduced B (fun i => (σ i).representation)) :=
  letI := T.topology
  Representation.Equiv.refl _

end Langlands.PadicField.TopologicalData

namespace Langlands.Parabolic

section EquivalenceAlgebra

universe uA uG uH uV uW uU

/-- The inverse of an equivalence of representations, with every structure argument read off
from the given equivalence rather than synthesized again. -/
abbrev equivSymm {A : Type uA} {G : Type uG} {V : Type uV} {W : Type uW}
    {_ : Semiring A} {_ : Monoid G} {_ : AddCommMonoid V} {_ : AddCommMonoid W}
    {_ : Module A V} {_ : Module A W}
    {ρ : Representation A G V} {σ : Representation A G W} (φ : ρ.Equiv σ) : σ.Equiv ρ :=
  φ.symm

/-- The composite of two equivalences of representations, with every structure argument read
off from the given equivalences. -/
abbrev equivTrans {A : Type uA} {G : Type uG} {V : Type uV} {W : Type uW} {U : Type uU}
    {_ : Semiring A} {_ : Monoid G} {_ : AddCommMonoid V} {_ : AddCommMonoid W}
    {_ : AddCommMonoid U} {_ : Module A V} {_ : Module A W} {_ : Module A U}
    {ρ : Representation A G V} {σ : Representation A G W} {τ : Representation A G U}
    (φ : ρ.Equiv σ) (ψ : σ.Equiv τ) : ρ.Equiv τ :=
  φ.trans ψ

/-- Precomposing both actions with a monoid homomorphism preserves an equivalence. -/
abbrev equivPrecomp {A : Type uA} {G : Type uG} {H : Type uH} {V : Type uV} {W : Type uW}
    {_ : Semiring A} {_ : Monoid G} {_ : Monoid H} {_ : AddCommMonoid V} {_ : AddCommMonoid W}
    {_ : Module A V} {_ : Module A W}
    {ρ : Representation A G V} {σ : Representation A G W} (φ : ρ.Equiv σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  Representation.Equiv.mk φ.toLinearEquiv fun h => φ.isIntertwining' (f h)

end EquivalenceAlgebra

end Langlands.Parabolic

namespace Langlands.Parabolic

open GeneralLinear Geometric Shahidi

section Pairs

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Two bundled smooth factors as a family over the blocks of `![a, b]`. -/
def pairSmoothFamily {a b : ℕ}
    (σ1 : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (σ2 : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ∀ i : Fin 2, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (![a, b] i) F.Carrier)
  | 0 => σ1
  | 1 => σ2

/-- A two-block product of the bundled pair is the product of the literal pair family. -/
def pairSmoothFamilyProductEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (σ1 : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (σ2 : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (T.normalizedProductInduced (twoBlocks a b ha hb)
        (fun i => (pairSmoothFamily T σ1 σ2 i).representation))
      (T.normalizedProductInduced (twoBlocks a b ha hb)
        (pairFamily σ1.representation σ2.representation)) :=
  letI := T.topology
  T.normalizedProductInducedEquiv (twoBlocks a b ha hb) (fun i =>
    match i with
    | 0 => Representation.Equiv.refl _
    | 1 => Representation.Equiv.refl _)

end Pairs

section Regroupings

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (regrouping : OrderedProductRegrouping.{uF, max uF uW} F T)
variable (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
variable (σ0 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear C F.Carrier))
variable (σ1 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear A F.Carrier))
variable (σ2 : letI := T.topology; SmoothRep.{0,uF,max uF uW} ℂ (GeneralLinear B F.Carrier))

/-- Regrouping the three-block product as `C, (A, B)`. -/
def leftRegroupingEquiv :
    letI := T.topology
    Representation.Equiv
      ((T.normalizedProductInductionFunctor.{uF, max uF uW}
        (threeBlocks C A B hC hA hB)).obj (threeBlockSmoothFamily σ0 σ1 σ2)).representation
      (T.normalizedProductInduced (twoBlocks C (A + B) hC (Nat.add_pos_left hA B))
        (pairFamily σ0.representation
          (T.normalizedProductInduced (twoBlocks A B hA hB)
            (pairFamily σ1.representation σ2.representation)))) :=
  letI := T.topology
  T.normalizedProductRegroupingToEquiv regrouping
    (threeBlocks C A B hC hA hB) (twoBlocks C (A + B) hC (Nat.add_pos_left hA B))
    (leftRefinement C A B hC hA hB) (leftLabelEquiv C A B hC hA hB)
    (leftLabelEquiv_size C A B hC hA hB) (leftLabelEquiv_index C A B hC hA hB)
    (threeBlockSmoothFamily σ0 σ1 σ2)
    (pairFamily σ0.representation
      (T.normalizedProductInduced (twoBlocks A B hA hB)
        (pairFamily σ1.representation σ2.representation))) (fun j =>
      match j with
      | 0 => (T.normalizedProductInductionFamilyEqEquiv _ (by rfl)).trans
          ((T.normalizedProductInductionObjEquiv _ _).trans
            (T.singleBlockTransportedProductEquiv (leftRefinement C A B hC hA hB 0) rfl σ0))
      | 1 => (T.normalizedProductInductionFamilyEqEquiv _
            (by funext k; fin_cases k <;> rfl)).trans
          ((T.normalizedProductInductionObjEquiv (leftRefinement C A B hC hA hB 1)
              (pairSmoothFamily T σ1 σ2)).trans
            (pairSmoothFamilyProductEquiv T hA hB σ1 σ2)))

/-- Regrouping the three-block product as `(C, A), B`. -/
def rightRegroupingEquiv :
    letI := T.topology
    Representation.Equiv
      ((T.normalizedProductInductionFunctor.{uF, max uF uW}
        (threeBlocksRight C A B hC hA hB)).obj (threeBlockSmoothFamily σ0 σ1 σ2)).representation
      (T.normalizedProductInduced (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB)
        (pairFamily
          (T.normalizedProductInduced (twoBlocks C A hC hA)
            (pairFamily σ0.representation σ1.representation))
          σ2.representation)) :=
  letI := T.topology
  T.normalizedProductRegroupingToEquiv regrouping
    (threeBlocksRight C A B hC hA hB) (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB)
    (rightRefinement C A B hC hA hB) (rightLabelEquiv C A B hC hA hB)
    (rightLabelEquiv_size C A B hC hA hB) (rightLabelEquiv_index C A B hC hA hB)
    (threeBlockSmoothFamily σ0 σ1 σ2)
    (pairFamily
      (T.normalizedProductInduced (twoBlocks C A hC hA)
        (pairFamily σ0.representation σ1.representation))
      σ2.representation) (fun j =>
      match j with
      | 0 => (T.normalizedProductInductionFamilyEqEquiv _
            (by funext k; fin_cases k <;> rfl)).trans
          ((T.normalizedProductInductionObjEquiv (rightRefinement C A B hC hA hB 0)
              (pairSmoothFamily T σ0 σ1)).trans
            (pairSmoothFamilyProductEquiv T hC hA σ0 σ1))
      | 1 => (T.normalizedProductInductionFamilyEqEquiv _ (by rfl)).trans
          ((T.normalizedProductInductionObjEquiv _ _).trans
            (T.singleBlockTransportedProductEquiv (rightRefinement C A B hC hA hB 1) rfl σ2)))

/-- The three-block product at total rank `C + (A + B)` transported to `(C + A) + B`. -/
def threeBlockRankCastEquiv :
    letI := T.topology
    Representation.Equiv
      (((T.normalizedProductInductionFunctor.{uF, max uF uW}
        (threeBlocks C A B hC hA hB)).obj (threeBlockSmoothFamily σ0 σ1 σ2)).representation.comp
          (reindex (R := F.Carrier) (finCongr (Nat.add_assoc C A B))).toMonoidHom)
      ((T.normalizedProductInductionFunctor.{uF, max uF uW}
        (threeBlocksRight C A B hC hA hB)).obj (threeBlockSmoothFamily σ0 σ1 σ2)).representation :=
  letI := T.topology
  T.normalizedProductInductionRankCastEquiv (Nat.add_assoc C A B)
    (threeBlocks C A B hC hA hB) (threeBlockSmoothFamily σ0 σ1 σ2)

/-- The two bracketings of three smooth factors are equivalent after the entry-preserving
rank cast, given ordered regrouping. -/
def threeBlockAssociativityEquiv :
    letI := T.topology
    Representation.Equiv
      ((T.normalizedProductInduced (twoBlocks C (A + B) hC (Nat.add_pos_left hA B))
        (pairFamily σ0.representation
          (T.normalizedProductInduced (twoBlocks A B hA hB)
            (pairFamily σ1.representation σ2.representation)))).comp
        (reindex (R := F.Carrier) (finCongr (Nat.add_assoc C A B))).toMonoidHom)
      (T.normalizedProductInduced (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB)
        (pairFamily
          (T.normalizedProductInduced (twoBlocks C A hC hA)
            (pairFamily σ0.representation σ1.representation))
          σ2.representation)) :=
  letI := T.topology
  equivTrans
    (equivPrecomp
      (equivSymm (leftRegroupingEquiv.{uF, uW} T regrouping C A B hC hA hB σ0 σ1 σ2))
      (reindex (R := F.Carrier) (finCongr (Nat.add_assoc C A B))).toMonoidHom)
    (equivTrans (threeBlockRankCastEquiv.{uF, uW} T C A B hC hA hB σ0 σ1 σ2)
      (rightRegroupingEquiv.{uF, uW} T regrouping C A B hC hA hB σ0 σ1 σ2))

end Regroupings

universe uF uW

/-- Common-universe three-block associativity follows from ordered product regrouping. -/
theorem commonUniverseThreeBlockAssociativity_of_regrouping
    (regrouping : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      OrderedProductRegrouping.{uF, max uF uW} F F.canonicalTopologicalData) :
    CommonUniverseThreeBlockAssociativity.{uF, uW} := by
  intro p _ F C A B hC hA hB W0 W1 W2 _ _ _ _ _ _ τ0 τ1 τ2 _ hτ0 hτ1 hτ2
  exact ⟨threeBlockAssociativityEquiv.{uF, uW} F.canonicalTopologicalData (regrouping p F)
    C A B hC hA hB (SmoothRep.of τ0 hτ0) (SmoothRep.of τ1 hτ1) (SmoothRep.of τ2 hτ2)⟩

end Langlands.Parabolic
