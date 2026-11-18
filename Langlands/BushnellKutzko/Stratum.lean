import Langlands.BushnellKutzko.UnitFiltration

/-! # Strata and their equivalence (BK93 (1.5.1), printed p. 43) -/

namespace Langlands.BushnellKutzko

universe uO uK uV

variable (O : Type uO) (K : Type uK) (V : Type uV) [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- A stratum `[𝔄,n,r,b]`, with its hereditary order represented by a published
lattice chain, integers `n > r`, and `v_𝔄(b) ≥ −n` (BK93 p. 43). -/
structure Stratum where
  chain : LatticeChain O K V
  n : ℤ
  r : ℤ
  b : Module.End K V
  r_lt_n : r < n
  valuation_ge : (-n : WithTop ℤ) ≤ chain.valuation b

namespace Stratum

variable {O K V}

/-- The coset `b + 𝔓^{−r}` attached to a stratum (BK93 (1.5.1), p. 43). -/
def coset (S : Stratum O K V) : Set (Module.End K V) :=
  {x | x - S.b ∈ S.chain.endFiltration (-S.r)}

/-- Two strata are equivalent precisely when their cosets coincide
(BK93 (1.5.1), p. 43). -/
def Equivalent (S T : Stratum O K V) : Prop :=
  S.coset = T.coset

end Stratum

end Langlands.BushnellKutzko
