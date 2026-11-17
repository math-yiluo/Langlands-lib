# Module sheaves from compatible modules on all affine tests

Lean module: `Langlands.AlgebraicGeometry.Modules.AffineTestRealization`.

## The data: `AffineTestSystem S`

For a scheme `S`, an `AffineTestSystem S` consists of

- `obj`: for every commutative ring `R` and every morphism `a : Spec R ⟶ S` (an *affine test*),
  an `R`-module `obj a`;
- `ext`: for every `R`-algebra `A`, every pair of tests `a : Spec R ⟶ S`, `b : Spec A ⟶ S` and
  every proof `h : Spec(R → A) ≫ a = b`, an `A`-linear isomorphism
  `ext h : A ⊗[R] obj a ≃ obj b` (coefficient extension);
- `ext_comp`: for a scalar tower `R → A → B` and tests `a, b, c` with
  `Spec(R → A) ≫ a = b`, `Spec(A → B) ≫ b = c`, `Spec(R → B) ≫ a = c`, the identity
  `ext_{ac}(1 ⊗ x) = ext_{bc}(1 ⊗ ext_{ab}(1 ⊗ x))` for all `x : obj a`.

The cocycle condition is only stated on elements `1 ⊗ x`; since these generate the tensor
products, this is the usual compatibility of the identifications with composition of ring
maps. No identity axiom is required: `map_id` below derives it from `ext_comp` and the
bijectivity of `ext`.

This is the familiar description of a quasi-coherent module on `S` as a compatible family of
modules on all affine schemes over `S` (equivalently, a cartesian module on the category of
affine `S`-schemes). Here only the data are recorded; the realization below turns them into an
actual sheaf of `𝒪_S`-modules.

## Coefficient extension along ring maps

- `map f h : obj a →ₛₗ[f] obj b`, for a ring map `f : R ⟶ A` and `h : Spec.map f ≫ a = b`, is
  `x ↦ ext h (1 ⊗ x)` with the algebra structure `f.toAlgebra`.
- `map_comp`: `map g (map f x) = map (f ≫ g) x`; `map_congr` changes the ring map along an
  equality; `map_id` / `map_eq_self`: `map (𝟙 R) x = x`.
- `ext_tmul_toAlgebra`: `ext h (s ⊗ x) = s • map f h x`.
- `map_surjective`: if `f` is surjective, so is `map f h`.
- `map_isLocalizedModule`: if `A` is the localization of `R` away from `r` (via `f`), then every
  `y : obj b` satisfies `map f h x = f (r ^ n) • y` for some `n` and `x`, and every `x` with
  `map f h x = 0` is killed by a power of `r`. (Proof: `A ⊗[R] obj a` is the localization of
  `obj a`, Mathlib's `tensorProduct_isLocalizedModule`, transported along `ext h`.)

## Affine opens

For affine opens `W ≤ V` of `S`, with canonical charts `hV.fromSpec : Spec Γ(S, V) ⟶ S`,
`res hV hW h : obj hV.fromSpec → obj hW.fromSpec` is `map` along the restriction
`Γ(S, V) → Γ(S, W)` (using `IsAffineOpen.map_fromSpec`). It satisfies `res_res`, `res_self`
and `res_smul` (semilinearity over the restriction map).

## The presheaf and its quasi-coherence

- `compat O` is the `Γ(S, O)`-module of families `(x_V)` indexed by the affine opens `V ≤ O`
  (`CoherentPresheafRealization.AffBelow O`), `x_V : obj hV.fromSpec` viewed as a
  `Γ(S, O)`-module by restriction of scalars, which are compatible:
  `res hV hW h x_V = x_W` for `W ≤ V`. `famVal x V` is the member at `V`.
- `evalEquiv hU : compat U ≃ₗ[Γ(S, U)] obj hU.fromSpec` (for affine `U`) evaluates at `U`
  itself; its inverse is `y ↦ (res hU hV y)_V`.
- `compatRes` is restriction of families; `presheaf : OModulePresheaf S.toSpecΓ` packages
  `O ↦ compat O` (over the base ring `Γ(S, ⊤)`) with these restrictions.
  `evalEquiv_presheaf_res` says evaluation turns restriction into `res`.
- `isQuasicoherent_presheaf`: this presheaf satisfies the project's
  `OModulePresheaf.IsQuasicoherent` (sections over a basic open `D(f)` of an affine open are the
  localization at `f`). This follows from `map_isLocalizedModule` and the Mathlib fact that
  `Γ(S, D(f))` is the localization of `Γ(S, U)` away from `f`
  (`IsAffineOpen.isLocalization_of_eq_basicOpen`).

## The realization

- `toModules : S.Modules` is `CoherentPresheafRealization.realization presheaf
  isQuasicoherent_presheaf`, the sheaf of compatible families over affine opens. No
  separatedness or noetherian hypothesis on `S` is needed.
- `sectionsEquiv hU : Γ(toModules, U) ≃ₗ[Γ(S, U)] obj hU.fromSpec` for every affine open `U`,
  and `sectionsEquiv_naturality`: for affine `V ≤ U`, it carries restriction of sections to
  `res hU hV`.
- `ofFamily x : Γ(toModules, O)` builds a section over an arbitrary open `O` from a compatible
  family `x : compat O`; `sectionsEquiv_res_ofFamily` says its restriction to every affine
  `V ≤ O` corresponds to `famVal x V`.
- `isQuasicoherent_toModules` (instance): the realization is quasi-coherent. On each canonical
  chart of an affine open the restriction is localizing
  (`CoherentPresheafRealization.isLocalizing_restrict`), hence isomorphic to the tilde of its
  global sections (Mathlib's `isIso_fromTildeΓ_iff_isLocalizing`,
  `isQuasicoherent_iff_isIso_fromTildeΓ`), and quasi-coherence is local
  (`IntegralIdealFiltration.isQuasicoherent_of_affine_nbhds`).

## Provenance

Internal construction for the task constructing root-weight line bundles over arbitrary base
schemes: the root-weight modules are naturally defined on every affine test `Spec R ⟶ S` with
canonical base-change identifications, and this module turns any such system into an actual
quasi-coherent sheaf of modules. Mathematically it is the standard equivalence between
quasi-coherent modules on `S` and compatible systems of modules on affine `S`-schemes
(restricted here to the direction needed: from the system to the sheaf).
