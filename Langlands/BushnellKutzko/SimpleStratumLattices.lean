import Langlands.BushnellKutzko.DefiningSequence

/-! # The lattices of a simple stratum (BK93 (3.1.7)–(3.1.8), printed pp. 90–91) -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uF uV

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V

/-- The depth `r = −k₀(β,𝔄)` from BK93 (3.1.6), with `r = ∞` in the scalar case. -/
def simpleCriticalDepth (L : LatticeChain O F V) (β : A) : WithTop ℤ :=
  match criticalExponent L β with
  | none => ⊤
  | some k => ((-k : ℤ) : WithTop ℤ)

/-- Integer value of the critical depth, with a fallback used only to totalize
finite-depth formulas. The terminal lattice formulas use `n`, not `r`. -/
def finiteCriticalDepth (L : LatticeChain O F V) (n : ℤ) (β : A) : ℤ :=
  (simpleCriticalDepth L β).untopD n

/-- The two cutoffs of (3.1.7)–(3.1.8), respectively. -/
def simpleHCutoff (r : ℤ) : ℤ := r / 2 + 1

/-- The cutoff of (3.1.8). -/
def simpleJCutoff (r : ℤ) : ℤ := (r + 1) / 2

namespace Stratum

/-- A choice of a BK93 (2.4.2) defining sequence with its first element equal
to the given element, not just equivalent to it. This retains the actual `β`
when starting the induction for (3.1.7)–(3.1.8). -/
structure DefiningSequenceChoice (S : Stratum O F V) where
  steps : ℕ
  terms : Fin (steps + 1) → Stratum O F V
  isDefiningSequence : S.IsDefiningSequence terms
  firstElement : (terms 0).b = S.b

/-- The successive elements after the initial element of a defining sequence. -/
def DefiningSequenceChoice.tail {S : Stratum O F V} (q : S.DefiningSequenceChoice) : List A :=
  List.ofFn fun i : Fin q.steps => (q.terms i.succ).b

/-- `T = [𝔄,n,r,γ]` is a simple equivalent to `[𝔄,n,r,β]` at the finite
critical depth of `β` (the approximation used in (3.1.7)(ii)). -/
def IsCriticalApproximation (S T : Stratum O F V) : Prop :=
  T.chain.order = S.chain.order ∧ T.n = S.n ∧ T.IsSimple ∧
    criticalExponent S.chain S.b = ((-T.r : ℤ) : WithBot ℤ) ∧
    T.b - S.b ∈ S.chain.endFiltration (-T.r)

end Stratum

/-- The pair `(ℌ(β,𝔄), 𝔍(β,𝔄))` from (3.1.7)–(3.1.8), computed from
`β` and the tail of a defining sequence. Recursion is structural on that tail. -/
def simpleStratumLattices (L : LatticeChain O F V) (n : ℤ) :
    A → List A → Submodule O A × Submodule O A
  | β, [] =>
      (centralizerLattice L β 0 ⊔ L.endFiltration (simpleHCutoff n),
       centralizerLattice L β 0 ⊔ L.endFiltration (simpleJCutoff n))
  | β, γ :: tail =>
      let r := finiteCriticalDepth L n β
      let next := simpleStratumLattices L n γ tail
      (centralizerLattice L β 0 ⊔ (next.1 ⊓ L.endFiltration (simpleHCutoff r)),
       centralizerLattice L β 0 ⊔ (next.2 ⊓ L.endFiltration (simpleJCutoff r)))

/-- The lattice `ℌ(β,𝔄)` computed from the supplied tail. -/
abbrev simpleHLattice (L : LatticeChain O F V) (n : ℤ) (β : A) (tail : List A) : Submodule O A :=
  (simpleStratumLattices L n β tail).1

/-- The lattice `𝔍(β,𝔄)` computed from the supplied tail. -/
abbrev simpleJLattice (L : LatticeChain O F V) (n : ℤ) (β : A) (tail : List A) : Submodule O A :=
  (simpleStratumLattices L n β tail).2

/-- The filtered lattice `ℌ^k = ℌ ∩ 𝔓^k` of BK93, printed p. 91. -/
def simpleHLayer (L : LatticeChain O F V) (n : ℤ) (β : A) (tail : List A) (k : ℕ) :
    Submodule O A :=
  simpleHLattice L n β tail ⊓ L.endFiltration k

/-- The filtered lattice `𝔍^k = 𝔍 ∩ 𝔓^k` of BK93, printed p. 91. -/
def simpleJLayer (L : LatticeChain O F V) (n : ℤ) (β : A) (tail : List A) (k : ℕ) :
    Submodule O A :=
  simpleJLattice L n β tail ⊓ L.endFiltration k

end Langlands.BushnellKutzko
