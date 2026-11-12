# Weil maps between relative global Weil groups

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. The module defines Artin and
Tate's *Weil maps* `W_{L/F} → W_{K/F}` between the published relative Weil groups
and proves their intrinsic properties. These maps are the transition maps of the
projective limit that defines the absolute Weil group (see
`Langlands.ClassField.Global.AbsoluteWeilGroup`). No Weil map is constructed here,
and no existence statement is made or assumed.

## Setting

Fix a class family `c : FundamentalClass.ClassFamily.{u}` and number fields
`F K L : Type u` with algebras `F → K`, `F → L`, `K → L`, the instance
`[IsScalarTower F K L]`, and both `K / F` and `L / F` Galois. Write

- `W_{L/F} := RelativeWeilGroup c F L`, the published class-indexed extension of
  `Gal(L/F)` by `C_L = IdeleClassGroup (𝓞 L) L` at the class `c F L`, with its
  published topology, `inclusion`, `projection`, `conjugation` and `exact`;
- `transfer c K L : W_{L/K} →* C_K`, the published transfer of
  `Langlands.ClassField.Global.RelativeWeilTransfer`;
- `restrictionInclusion c F L K h : W_{L/K} →ₜ* W_{L/F}`, the published comparison
  for `h : FundamentalClass.Restriction c`.

As in the imported modules, `relativeIdeleClassAction` and the discrete topology
`relativeGaloisTopology` on finite Galois groups are local instances. Everything
lives in the single universe `u` of the published relative Weil groups.
`W_{L/F}` is a relative Weil group in the sense of the sources only when
`c F L` is the arithmetic fundamental class. All results below hold for every
class family.

## Declarations

### Conjugation and coboundaries

- `conjMap x φ`, for a topological group `G` and `φ : G →ₜ* W_{K/F}`, is `φ` followed by
  conjugation by `x : W_{K/F}`. `conjMap_apply` gives `conjMap x φ g = x * φ g * x⁻¹`.
- `exists_eq_div_of_cocycle`: if `g : Gal(K/F) → C_K` satisfies
  `g (σ * τ) = g σ * σ(g τ)`, where `σ` acts by the published `relativeIdeleClassAut`,
  then there is `b : C_K` with `g σ = σ(b) / b` for all `σ`. The proof is the
  published `ideleClassH1Vanishing`, which proves that `H¹(Gal(K/F), C_K)` is a
  subsingleton. The cocycle is converted into Mathlib's
  `groupCohomology.cocycles₁` of the published `relativeIdeleClassRepresentation`.

### The subgroup `U^L_K` and its commutator closure

These declarations need only `NumberField F`, `NumberField L` and `IsGalois F L`;
the statements about kernels also need `Normal F K`.

- `range_restrictScalarsHom_eq_ker` (for any tower of fields `F ⊆ K ⊆ L` with
  `K / F` and `L / F` normal): the image of `AlgEquiv.restrictScalarsHom F :
  Gal(L/K) → Gal(L/F)` is the kernel of `AlgEquiv.restrictNormalHom K :
  Gal(L/F) → Gal(K/F)`. A `K`-linear automorphism restricts to the identity of
  `K`. Conversely, an automorphism restricting to the identity is `K`-linear and
  is rebuilt by `AlgEquiv.ofRingEquiv`.
- `levelSubgroup c F K L` is Artin–Tate's `U^L_K = g⁻¹(Gal(L/K))`. In Lean it is the
  inverse image under `projection c F L` of the range of
  `AlgEquiv.restrictScalarsHom F`. `mem_levelSubgroup_iff` unfolds membership.
- `levelSubgroup_eq_ker` identifies it with the kernel of
  `W_{L/F} → Gal(L/F) → Gal(K/F)`, and
  `mem_levelSubgroup_iff_restrictNormalHom` states membership as
  `(projection t)|_K = 1`. The instance `levelSubgroup_normal` follows.
- `inclusion_mem_levelSubgroup`: `C_L ⊆ U^L_K`.
- `levelCommutatorClosure c F K L` is `(U^L_K)^c`, the topological closure in
  `W_{L/F}` of the commutator subgroup `⁅U^L_K, U^L_K⁆`. It is normal
  (`levelCommutatorClosure_normal`, Mathlib's closure of a normal subgroup) and is
  contained in `U^L_K` (`levelCommutatorClosure_le_levelSubgroup`), because `U^L_K`
  is the preimage of a point under a continuous map to a discrete group.
- `range_restrictionInclusion_eq_levelSubgroup` (with `NumberField K` and
  `h : FundamentalClass.Restriction c`): the published range theorem
  `range_restrictionInclusion`, written with `levelSubgroup`.

### Weil maps

`IsWeilMap c F K L h φ`, for `φ : W_{L/F} →ₜ* W_{K/F}`, is the structure with the
four fields

1. `surjective`: `φ` is surjective;
2. `projection_map`: `projection c F K (φ t) =
   AlgEquiv.restrictNormalHom K (projection c F L t)` for every `t`;
3. `map_restrictionInclusion`: `φ (restrictionInclusion c F L K h t) =
   inclusion c F K (transfer c K L t)` for every `t : W_{L/K}`;
4. `ker_eq`: the kernel of `φ` is `levelCommutatorClosure c F K L`.

Continuity is part of the type `→ₜ*`.

### Proved properties

Let `hφ hψ : IsWeilMap c F K L h _`.

- `IsWeilMap.map_inclusion`: `φ (inclusion c F L a) =
  inclusion c F K (ideleClassNorm (K := K) (L := L) a)`. On `C_L` a Weil map is the
  idele-class norm. Since `restrictionInclusion` fixes `C_L`, this is field 3
  combined with the published `transfer_inclusion`.
- `IsWeilMap.map_mem_range_inclusion`: `φ` maps `U^L_K` into `C_K`.
- `IsWeilMap.levelSubgroup_eq_comap`: `U^L_K` is the inverse image of `C_K` under `φ`.
  This uses field 2 and the published exactness `range inclusion = ker projection`.
- `IsWeilMap.commutator_le_ker`: `⁅U^L_K, U^L_K⁆ ≤ ker φ`.
- `IsWeilMap.isOpenMap`: `φ` is an open map. Near a point `φ t` of the image of an
  open set `U`, the image contains the translate by `φ t` of the norm image of an open
  neighbourhood of `1` in `C_L`. The proof uses `map_inclusion`, the published
  openness of the idele-class norm (`isOpenMap_ideleClassNorm`), the published open
  embedding `inclusion c F K` and openness of right translation.
- `IsWeilMap.quotientEquiv : W_{L/F} ⧸ levelCommutatorClosure c F K L ≃ₜ* W_{K/F}` is
  the induced isomorphism of topological groups, with `quotientEquiv_mk` giving
  `quotientEquiv (mk t) = φ t`. Algebraically it composes
  `QuotientGroup.quotientMulEquivOfEq` (field 4) with
  `QuotientGroup.quotientKerEquivOfSurjective` (field 1). It is continuous through
  the quotient map and open because `φ` is open. The quotient carries Mathlib's
  quotient topology.
- `IsWeilMap.conj`: for `a : C_K`, `conjMap (inclusion c F K a) φ` is again a Weil map.
  Conjugation by `a` fixes the projection, because `inclusion a` projects to `1`. It
  fixes the values on `U^L_K`, because these lie in the commutative image of `C_K`.
  It does not change the kernel.
- `IsWeilMap.eq_of_mem_levelSubgroup`: two Weil maps agree on `U^L_K`.
- `IsWeilMap.exists_eq_conjMap`: for Weil maps `φ ψ` there is `a : C_K` with
  `ψ = conjMap (inclusion c F K a) φ`. The proof sets
  `d t = ψ t * (φ t)⁻¹ ∈ C_K`, which is defined because both maps have the same
  projection. Then `d` satisfies `d (s * t) = d s * (r s)(d t)`, where
  `r : W_{L/F} → Gal(K/F)` is the composite of the projection and the restriction,
  and `d` is right `U^L_K`-invariant. Hence `d` descends along the surjection `r` to a
  cocycle `g` of `Gal(K/F)`. By `exists_eq_div_of_cocycle`, `g σ = σ(b)/b`, and then
  `a = b⁻¹` works.

## Source correspondence

E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea 2009, literature ID
`artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. The PDF page
is the printed page plus nine. The following passages of Chapter XV were read
from the original.

- Definition 1, printed p.167 (PDF p.176): a Weil group `(U, g, {f_E})` of a layer
  `K/F`, with `U_E = g⁻¹(G_{K/E})` and `f_E : A_E ≅ U_E/U_E^c`.
- Definition 2, printed pp.169–170 (PDF pp.178–179): a Weil isomorphism satisfies
  WI1 (compatibility with `g`) and WI2 (compatibility with every `f_E`).
- Theorem 2 and its proof, printed pp.170–171 (PDF pp.179–180). The proof reduces
  WI2 to the case `E = K`. It also shows that the maps are unique up to inner
  automorphisms by elements of `U′_K = A_K`, because `H¹(G_{K/F}, A_K) = 0`.
- Theorem 3, printed p.171 (PDF p.180): for a big layer `K₁/F₁` and a normal
  sub-layer `K/F`, the group `U_F/U_K^c` is a Weil group for `K/F`.
- Printed p.177 (PDF p.186): a *Weil map* `ϕ_{L/K} : U^L → U^K` is a homomorphism
  with kernel `(U^L_K)^c` inducing a Weil isomorphism
  `U^L/(U^L_K)^c ≅ U^K`. The lemma on that page states that `ϕ_{L/K}` restricts to
  `N_{L/K}` on `A_L`, and that it is a topological homomorphism exactly when the
  norm is open. The text below the lemma says that a Weil map is unique up to inner
  automorphisms of `U^K` by elements of `A_K`.
- Printed p.178 (PDF p.187): the set `X_{L,K}` of Weil maps consists of the maps
  `a_K ϕ⁰` for `a ∈ A_K`.
- Printed p.175 (PDF p.184), Definition 3: in the topological setting `U_F^c`
  denotes the *closure* of the commutator subgroup.

J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, §1.1–1.2,
printed pp.3–5 (PDF pp.12–14), was also read. It describes `W_{E/F} = W_F/W_E^c` and
diagram (1.2.2), in which inclusion and transfer correspond to the norm. §1.2 says
the projective-limit construction is carried out in Artin–Tate.

### Derived formulation

1. **Unpackaged Weil structures.** Artin–Tate's `U^L` and `U^K` carry isomorphisms
   `f_E`, and `f_E` is the inverse of the transfer (Theorem 1, printed pp.168–169).
   The published `RelativeWeilGroup` is the bare class extension, for an arbitrary
   class family. Its transfer is published separately; that it induces
   `W^{ab} ≅ C` is the published `RelativeWeilTransferReciprocityStatement`, proved
   as `relativeWeilTransferReciprocity` for fundamental-class families and not used
   here. So `IsWeilMap` imposes WI1 as
   field 2 and WI2 only at `E = K`, as field 3. That is the condition to which the
   proof of Theorem 2 reduces WI2. On `U^L_K` the quotient Weil group has
   `f_K = (transfer)⁻¹` and `U^K` has `f′_K = inclusion`, so WI2 at `K` says exactly
   that `φ` equals the inclusion of the transfer on `U^L_K`. Fields 1 and 4 say that
   `φ` has kernel `(U^L_K)^c` and induces an isomorphism.
2. **Parametrization of `U^L_K`.** Field 3 is stated through the published
   comparison `restrictionInclusion c F L K h : W_{L/K} → W_{L/F}`, whose range is
   `U^L_K`. That comparison is built from a chosen representative and is the
   identity on `C_L`. Transfer is natural under isomorphisms that carry `C_L`
   identically, so the condition does not depend on this choice. This independence
   is a mathematical remark and is not proved in Lean. The hypothesis `h` enters
   only through `restrictionInclusion`.
3. **Closure.** The kernel is the topological closure of the commutator subgroup,
   as in Definition 3. Artin–Tate show that in finite layers the commutator
   subgroup is already closed (lemma on printed p.176), but that fact is not used.
4. **Uniqueness input.** The uniqueness theorem uses the published vanishing of
   `H¹(Gal(K/F), C_K)` for every finite Galois extension of number fields. It needs
   no hypothesis on the class family.

## Scope and remaining obligations

This module proves no existence statement. It does not prove that Weil maps exist
for the arithmetic fundamental-class family. That needs the class of the extension
`C_K ≅ U^L_K/(U^L_K)^c → W_{L/F}/(U^L_K)^c → Gal(K/F)` to be `c F K`, which is
Artin–Tate's W3 for the quotient and the Akizuki–Witt identity of XIII §3,
Theorem 6. It also does not prove that composites of Weil maps are Weil maps. These
are theorem obligations over the published fundamental-class results
(`globalFundamentalClassStatement` and `relativeWeilTransferReciprocity`); they are
neither used nor assumed here. The absolute limit over transitive systems of Weil
maps is constructed in `Langlands.ClassField.Global.AbsoluteWeilGroup`.
