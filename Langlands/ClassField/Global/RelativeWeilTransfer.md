# The transfer from relative global Weil groups to idele classes

Worker 35 wrote this definition unit, items 1–5 of task
fe42e5e4-f578-4b3e-a8b5-efb4ea3a0cc6. On the operator's instruction it is
submitted under task 91266440-3276-48dc-ab77-8d1c1fa386e8. The module
`Langlands.ClassField.Global.RelativeWeilTransfer` constructs the transfer
`W_{E/F} → C_F` on the published relative global Weil groups. It proves that
the transfer to `C_E` has Galois-fixed values, descends it to `C_F`, and proves
the norm formula. Every declaration accepts an arbitrary class family `c`.
No fundamental-class hypothesis is used, and no normalization is claimed in
Lean. The reciprocity statement `W_{E/F}^{ab} ≅ C_F` at the arithmetic classes
is the separate statement unit
`Langlands.ClassField.Global.RelativeWeilTransferReciprocityStatement`.

## Objects

Throughout, `c : FundamentalClass.ClassFamily.{u}` is arbitrary, and
`F E : Type u` are number fields with `[Algebra F E] [IsGalois F E]`.
Write

- `W := RelativeWeilGroup c F E`, the published abbreviation for
  `ClassExtension (K := F) (c F E)`, with the published `inclusion`,
  `projection`, `inclusion_injective`, `projection_surjective`, `exact`,
  `isOpenEmbedding_inclusion`, `conjugation` and `index_range_inclusion`;
- `C_E := IdeleClassGroup (𝓞 E) E` and `C_F := IdeleClassGroup (𝓞 F) F`;
- `ideleClassInclusion (K := F) (L := E) : C_F → C_E` and
  `ideleClassNorm (K := F) (L := E) : C_E → C_F`, the published maps of
  `Langlands.Global.AdelicFunctoriality`;
- `relativeIdeleClassAut F E σ`, the published action of `σ : E ≃ₐ[F] E` on
  `C_E`.

As in `Langlands.ClassField.Global.RelativeWeilGroup`, the action
`relativeIdeleClassAction` and the discrete topology `relativeGaloisTopology`
on `E ≃ₐ[F] E` are local instances. The module introduces no new carrier,
quotient, supplied subgroup or supplied extension. All declarations live in
the single universe `u`. The published proofs are used at
`ideleClassGaloisDescent.{u, u}` and `ideleClassNormGaloisProduct.{u, u}`.

## General transfer lemmas

The namespace `Langlands.GroupTheory.Transfer` proves facts about Mathlib's
`MonoidHom.transfer` that Mathlib lacks. Here `G` is a group, `H` a subgroup,
and `A`, `B` are commutative groups.

- `transfer_comp`: for `ϕ : H →* A` and `f : A →* B`, the transfer of
  `f.comp ϕ` is `f` applied to the transfer of `ϕ`, when `H` has finite index.
  Both sides are computed with the same left transversal through
  `MonoidHom.transfer_def`, and `f` commutes with finite products.
- `conjInv v : H →* H`, for normal `H` and `v : G`, is `h ↦ v⁻¹ * h * v`.
  `coe_conjInv` records its value in `G`.
- `diff_op_smul`: right translation by `v` of two left transversals of a normal
  subgroup turns their difference `Subgroup.leftTransversals.diff ϕ` into the
  difference for `ϕ.comp (conjInv v)`.
- `transfer_comp_conjInv`: for normal `H` of finite index,
  `MonoidHom.transfer (ϕ.comp (conjInv v)) g = MonoidHom.transfer ϕ g`. The
  proof computes the left side with a transversal `T` and the right side with
  `T v`, applies `diff_op_smul`, and uses that right translation commutes with
  the left action of `g`. This is the naturality of the transfer under the
  inner automorphism of `v`, the rule `V_{U,uWu⁻¹}(u') = u V_{U,W}(u') u⁻¹` of
  Artin–Tate XIII §2 (printed p.133), specialized to a normal subgroup.
- `smul_quotient_of_mem`: an element of a normal subgroup fixes every left
  coset.
- `transfer_of_mem`: for normal `H` of finite index, a left transversal `T`
  and `h : H`, the transfer of `h` is
  `∏ q : G ⧸ H, ϕ (t_q⁻¹ * h * t_q)`, where `t_q` is the element of `T` in the
  coset `q`. This is the remark after Tate's (1.2.2) (printed p.4): on a normal
  subgroup, the transfer is the product of the conjugates by coset
  representatives.

## Declarations

### Item 1: the idele-class subgroup

- `ideleClassSubgroup c F E : Subgroup W` is the abbreviation for
  `(inclusion c F E).range`.
- The instance `ideleClassSubgroup_finiteIndex` holds because the index is
  `Module.finrank F E` by `index_range_inclusion`, and this is positive.
- The instance `ideleClassSubgroup_normal` holds because the range is the
  kernel of `projection c F E` by `exact`.
- `isOpen_ideleClassSubgroup` holds because `inclusion c F E` is an open
  embedding, by `isOpenEmbedding_inclusion`.
- `ideleClassSubgroupEquiv c F E : ideleClassSubgroup c F E ≃ₜ* C_E` is the
  inverse of `MonoidHom.ofInjective (inclusion_injective c F E)`. The direction
  from the subgroup to `C_E` is continuous because composing it with the
  embedding `inclusion c F E` gives the subtype inclusion. The direction from
  `C_E` is continuous because `inclusion c F E` is continuous.
- `inclusion_ideleClassSubgroupEquiv` and `ideleClassSubgroupEquiv_inclusion`
  are its two composition identities with `inclusion c F E`.

### Item 2: the transfer to `C_E`

- `ideleTransfer c F E : W →ₜ* C_E` is exactly the published
  `Langlands.LocalClassField.continuousTransfer` of the module
  `Langlands.ClassFieldTheory.Local.Transfer`, applied to
  `ideleClassSubgroup c F E`, its openness, and `ideleClassSubgroupEquiv c F E`
  viewed as a continuous homomorphism.
- `ideleTransfer_apply` records, by `rfl`, that its underlying map is Mathlib's
  coset-product transfer `MonoidHom.transfer` of that identification.

Tate 1979 §1 (printed p.3) defines the transfer with right cosets `H\G`, and
Artin–Tate XIII §2 (printed p.132) writes it with representatives `u_σ`.
Mathlib uses left cosets `G ⧸ H`. For a commutative target the two products
define the same homomorphism. Use the right transversal of inverses of a left
transversal: the right-coset transfer of `g` is then the inverse of the
left-coset transfer of `g⁻¹`. This identification of conventions is explained
here and is not formalized.

### Item 3: Galois-fixed values

`relativeIdeleClassAut_ideleTransfer` proves

`∀ (σ : E ≃ₐ[F] E) (t : W), relativeIdeleClassAut F E σ (ideleTransfer c F E t) = ideleTransfer c F E t`.

The proof chooses `u : W` with `projection c F E u = σ`. The published
`conjugation` shows that `ψ ∘ conjInv u⁻¹ = σ ∘ ψ`, where `ψ` is the
identification of item 1 and `conjInv u⁻¹` is `h ↦ u h u⁻¹`. Then
`transfer_comp_conjInv` and `transfer_comp` give the identity. Artin–Tate XV,
proof of Theorem 1 (printed p.168), cites XIII §2 for this fact.

### Item 4: the transfer on `C_E`

`ideleTransfer_inclusion` proves, for `a : C_E`,

`ideleTransfer c F E (inclusion c F E a) = ∏ σ : E ≃ₐ[F] E, relativeIdeleClassAut F E σ a`,

with the instance `Fintype.ofFinite (E ≃ₐ[F] E)`, as in the published
`IdeleClassNormGaloisProduct`. The proof applies `transfer_of_mem` to the
default left transversal and reindexes the product along the bijection
`q ↦ projection c F E (t_q⁻¹)` from `W ⧸ ideleClassSubgroup c F E` onto
`E ≃ₐ[F] E`. By `conjugation`, `t_q⁻¹ (inclusion a) t_q` is the inclusion of
the conjugate of `a` by that automorphism. This is the finite-level form of
Artin–Tate's computation `V_{U,A}(a) = N a` (XIII §2, printed p.132).

### Item 5: descent to `C_F`

- `ideleTransfer_mem_range` proves that every value of `ideleTransfer c F E`
  lies in the image of `ideleClassInclusion`. This follows from item 3 and the
  fixed-class half of the published `ideleClassGaloisDescent`.
- `transfer c F E : W →* C_F` is the corestriction of `ideleTransfer c F E` to
  that image, followed by the inverse of the injective map `ideleClassInclusion`.
- `ideleClassInclusion_transfer` is the characterization
  `ideleClassInclusion (transfer c F E t) = ideleTransfer c F E t`.
- `eq_transfer_of_ideleClassInclusion_eq` is uniqueness: any `x : C_F` with
  `ideleClassInclusion x = ideleTransfer c F E t` equals `transfer c F E t`.
- `transfer_inclusion` proves
  `transfer c F E (inclusion c F E a) = ideleClassNorm (K := F) (L := E) a`.
  It combines item 4, the published `ideleClassNormGaloisProduct` and the
  injectivity in `ideleClassGaloisDescent`.
- `commutator_le_ker_transfer` proves
  `commutator W ≤ (transfer c F E).ker`, because `C_F` is commutative.
- `continuous_transfer` proves that `transfer c F E` is continuous under the
  explicit hypothesis
  `Topology.IsEmbedding (ideleClassInclusion (K := F) (L := E))`.
  `continuousTransferOfEmbedding` packages it under that hypothesis as
  `W →ₜ* C_F`.

## Continuity

The module makes no unconditional continuity claim for `transfer c F E`. The
published `ideleClassGaloisDescent` is algebraic: it gives injectivity of
`C_F → C_E` and identifies its image with the Galois-fixed classes. It does not
give that `C_F → C_E` is a topological embedding, and this embedding is
unproved in the Library. The map to `C_E`, `ideleTransfer c F E`, is
continuous unconditionally.

## Frobenius convention (documentation only)

This section is not stated or proved in Lean. It records how
`transfer c F E` is normalized when `c F E` is the arithmetic fundamental class
`u_{E/F}` of Artin–Tate. It also compares it with Tate's `τ_F = r_F⁻¹`,
which Henniart 2000 §2.2 (printed p.444) uses in `det S = ω_Π ∘ τ_F`.

1. **Artin–Tate.** In the proof of XV Theorem 1 (printed pp.168–169), `U` is
   an extension of `G_{K/F}` by `A_K` with the fundamental class. The transfer
   `V_{K/E} : U_E/U_E^c → A_E` is shown to be an isomorphism, and `f_E` is
   defined as its inverse. Their layer `K/F` is our `E/F`, and their `U_F = U`
   is `W`. So `transfer c F E` is Artin–Tate's `V_{K/F}`, read through the
   identification of `C_F` with the Galois-fixed classes in `C_E`.
2. **Tate.** Tate's (W3) (printed p.4) says that for `E' ⊆ E` the transfer
   `W_{E'}^{ab} → W_E^{ab}` corresponds under `r_{E'}` and `r_E` to the
   inclusion `C_{E'} → C_E`. Take `E' = F` and pass to
   `W_{E/F} = W_F / W_E^c`, in which `r_E` identifies `W_E / W_E^c` with `C_E`
   (§1.2). Then `τ_F` on `W_{E/F}` is the transfer to the coefficient subgroup,
   computed with the identification `r_E⁻¹`, followed by descent to `C_F`.
3. **Comparison.** The published `LocalRelativeWeilMap.md`, in its section on
   the sign in condition 3, explains that Tate's canonical class is
   `a_{E/F} = -u_{E/F}`. Tate's `W_{E/F}` is equivalent to
   `ClassExtension (c F E)` when `c F E = u_{E/F}`, by an equivalence `Φ` that
   is compatible with the projections and sends `i_T(x)` to
   `(inclusion c F E x)⁻¹`. Under `Φ`, Tate's identification of the
   coefficient subgroup with `C_E` becomes `x ↦ (ideleClassSubgroupEquiv x)⁻¹`.
   The transfer is natural under group isomorphisms. By `transfer_comp`,
   composing the identification with inversion, a homomorphism of the
   commutative group `C_E`, inverts the transfer. Hence
   `transfer c F E (Φ w) = τ_F(w)⁻¹` for `w` in Tate's `W_{E/F}`: **the two
   maps differ by inversion.**
4. **Frobenius.** Tate (1.4.1) (printed p.6) normalizes `r_E` so that
   uniformizers correspond to the inverse of the Frobenius automorphism, which
   it notes is opposite to Artin–Tate. Let `v` be a finite place of `F`
   unramified in `E`, and let `Φ_v ∈ W_{F_v}` act as geometric Frobenius.
   Local-global compatibility (Tate (1.6.1)) gives that `τ_F` sends the image
   of `Φ_v` to the class of a uniformizer of `F_v`. So `transfer c F E` sends
   the image of an arithmetic Frobenius element to the class of a
   uniformizer. This is the arithmetic convention of Artin–Tate, the same
   normalization that condition 3 of the published
   `RelativeWeilGroup.IsLocalRelativeWeilMap` uses. Compatibility of
   `transfer` with local maps is not proved (see Out of scope). A consumer
   that needs Henniart's `τ_F` at finite level should use the inverse of
   `transfer c F E`.

## Out of scope

The following remaining prerequisites are not part of this unit.

- The proof of the reciprocity statement
  `RelativeWeilTransferReciprocityStatement`. It needs the
  Tate–Nakayama and class-formation cohomology of Artin–Tate XIII §2.
- Instantiating the fundamental-class family (task
  fb66219f-83c6-4b76-8bed-63bc57c07205).
- The topological embedding `C_F → C_E`.
- Norm and tower transition maps `W_{L/F} → W_{E/F}`, their compatibility with
  `transfer`, and the absolute group `W_F`. Worker 2 retains these in task
  6c50b2fd-cb4a-47b3-8f5d-d464916d69fb.
- Compatibility of `transfer` with the local maps
  `RelativeWeilGroup.localToRelative` and local reciprocity, and with the
  global Artin map.

## Sources

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33,
  Part II (1979), 3–26, source `tate-1979-number-theoretic-background`
  (PDF page = printed page + 9).
  - §1, printed p.3 (PDF p.12): the transfer of a closed subgroup of finite
    index, by coset products.
  - (W3) and the remark after (1.2.2), printed p.4 (PDF p.13): the transfer
    corresponds to the inclusion of idele classes. On a normal subgroup, the
    transfer is the product of the conjugates by coset representatives.
  - §1.2, printed pp.4–5 (PDF pp.13–14): the extension `W_{E/F}` of
    `Gal(E/F)` by `C_E` and its canonical class `a_{E/F}`.
  - (1.4.1), printed p.6 (PDF p.15): uniformizers correspond to inverse
    Frobenius, opposite to [AT].
- E. Artin and J. Tate, *Class Field Theory* (2009), source
  `artin-tate-2009-class-field-theory` (PDF page = printed page + 9).
  - Chapter XIII §2, printed pp.132–133 (PDF pp.141–142): the transfer
    `V_{U,A}`, its value `N a` on `A`, values in `A^G`, naturality under
    conjugation, Theorem 4 and its corollary.
  - Chapter XV §1, Definition 1 and Theorem 1 with its proof, printed
    pp.167–169 (PDF pp.176–178).
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique* (2000), source `henniart-2000-simple-proof`, §2.2,
  printed p.444: `det S = ω_Π ∘ τ_F`.
