# Products of standard unipotent radicals

Module `Langlands.Global.AdelicStandardUnipotentProduct`, namespace
`Langlands.Global.StandardConstantTerm`.

## Statement

`StandardUnipotentProductStatement`, proved by `standardUnipotentProduct`. Let `G` be connected
reductive over a field `k`, `i : T → G` a maximal split torus, `ν` a generic cocharacter, and
`J, K ⊆ Δ₀ = simpleRelativeRoots i ν`. Then on every test scheme `S`, every point of the standard
unipotent radical `U_{J ∩ K} = standardUnipotent i ν (J ∩ K)` is a product `u v` of a point
`u ∈ U_J(S)` and a point `v ∈ U_K(S)`.

For standard parabolics `R = P_J`, `Q = P_K` this is `U_{R ∩ Q} = U_R · U_Q` (`R ∩ Q` is the
standard parabolic `P_{J ∩ K}`). It is the structural input for the composition rule
`CT_R ∘ CT_Q = CT_{R ∩ Q}` of constant terms, which Bernstein–Lapid use in §7.3 (J. Amer. Math.
Soc. 37 (2024), p.214: "`CT_{P₁ ∩ P₂} = CT_{P₁} ∘ CT_{P₂}` (since `U_{P₁} U_{P₂} = U_{P₁ ∩ P₂}`)").
The reverse inclusion `U_J · U_K ⊆ U_{J ∩ K}` is not stated here.

## Proof

1. `isStandardCocharacter_add_inter`: if `ζ` is a standard cocharacter for `J` (zero on `J`,
   positive on `Δ₀ ∖ J`) and `ξ` is one for `K`, then `ζ + ξ` is one for `J ∩ K`. The pairing is
   additive, and standard cocharacters pair nonnegatively with every simple root.
2. `standardLevi_inf_standardUnipotent_inter_le`: `L_K ⊓ U_{J ∩ K} ≤ U_J` if `K` has a standard
   cocharacter `ξ`. Let `g ∈ L_K ⊓ U_{J ∩ K}`. For each standard `ζ` of `J`, `ζ + ξ` is standard
   for `J ∩ K`, so `g` lies in the dynamic unipotent group of `ζ + ξ`. Since `g` centralizes `ξ`,
   the Library's `Dynamic.mem_unipotent_add_iff_of_mem_centralizer` shows that `g` lies in the
   dynamic unipotent group of `ζ`. As `U_J` is the intersection of these groups over all standard
   `ζ`, `g ∈ U_J`.
3. `standardUnipotent_inter_subset_mul`: choose a standard cocharacter `ξ` of `K` that realizes
   `L_K` and `U_K` (from the Library's `standardCocharacter`). `standardParabolicOrder` gives
   `P_{J ∩ K} ≤ P_K` and `U_K ≤ U_{J ∩ K}`. The Library's
   `StandardLeviIntersection.standardUnipotent_eq_leviInter_mul` then writes
   `U_{J ∩ K} = (L_K ⊓ U_{J ∩ K}) · U_K`, and step 2 bounds the first factor by `U_J`.

## Scope

Only the inclusion on points is proved. The composition rule for constant terms and its
`L²` form are separate steps on the route to Bernstein–Lapid Theorem 7.2.
