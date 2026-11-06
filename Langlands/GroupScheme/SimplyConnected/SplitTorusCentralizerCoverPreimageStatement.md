# The preimage of a split-torus centralizer in a simply connected cover

Authors: Worker 1512 and Worker 1532; Markdown revised by Worker 1390.

`Langlands.GroupScheme.SplitTorusCentralizerCoverPreimageStatement.{u}`
is a proposition definition, not a proof. Let `G` be connected reductive,
`π : C → D` a central isogeny from a simply connected group onto the
derived subgroup `D` of `G`, and `M = Z_G(A)` the centralizer of a split
subtorus `A`. The statement says that the preimage `M'` of `M` in `C` is
again the centralizer of a split subtorus. It also says that the
restriction `p : M' → M` of `C → D → G` relates the rational characters,
the derived subgroups and suitable maximal tori of `M'` and `M` in the way
the proof of KP Corollary 2.6.28 uses.

## The proposition

For every field `k : Type u` and the following data and hypotheses over
`Spec k`:

- `G D C : GroupScheme (Spec (CommRingCat.of k))`, `d : D ⟶ G` and
  `π : C ⟶ D`, with `IsConnectedReductive G`, `IsDerivedSubgroup d`,
  `IsSimplyConnected C` and `IsCentralIsogeny π`;
- `A : CommGroupScheme (Spec (CommRingCat.of k))` and `a : A.toGrp ⟶ G`
  with `IsSplitSubtorus a`;
- `M` and `j : M ⟶ G` with `(torusCentralizer a).IsRepresentedBy j`;
- `DM CM`, `dM : DM ⟶ M` and `πM : CM ⟶ DM` with
  `IsSimplyConnectedDerivedCover dM πM`;
- `T : CommGroupScheme (Spec (CommRingCat.of k))` and `t : T.toGrp ⟶ M`
  with `IsMaximalTorus t`,

there exist `A'`, `a' : A'.toGrp ⟶ C`, `M'`, `j' : M' ⟶ C` and
`p : M' ⟶ M` such that:

1. `IsSplitSubtorus a'`, `(torusCentralizer a').IsRepresentedBy j'` and
   `IsConnectedReductive M'`;
2. `j' ≫ π ≫ d = p ≫ j`;
3. `SubgroupFunctor.range j' = (SubgroupFunctor.range j).comap (π ≫ d)`.
   On every test scheme, the points of `M'` are exactly the points of `C`
   whose image in `G` lies in `M`. So `M'` is the preimage of `M`;
4. for every `χ' : rationalCharacters M'` there are `n : ℕ` with `0 < n`
   and `χ : rationalCharacters M` with `n • χ' = characterRestrict p χ`;
5. there exist `D'`, `d' : D' ⟶ M'` and `b : D' ⟶ CM` with
   `IsDerivedSubgroup d'` and `b ≫ πM ≫ dM = d' ≫ p`;
6. there exist `T' : CommGroupScheme (Spec (CommRingCat.of k))`,
   `t' : T'.toGrp ⟶ M'` and `g : T' ⟶ T` with `IsMaximalTorus t'` and
   `t' ≫ p = CommGroupScheme.groupHom g ≫ t`, such that for every field
   `E : Type u` with `[Algebra k E]`, if the base change of `T` along
   `Spec E → Spec k` is a split torus, then so is the base change of
   `T'`.

These are all the quantified data and hypotheses. The universe `u` is
arbitrary. The field `k` has no perfectness, separability or
characteristic hypothesis, and `G` is not assumed quasi-split. The torus
`A` need not be maximal split. The cover `π` is only a central isogeny
from a simply connected group; its universal property
(`IsSimplyConnectedCover`) is not assumed. The cover `πM` of `M_der` does
carry the full `IsSimplyConnectedDerivedCover` predicate.

## Exact objects

- `GroupScheme S` and `CommGroupScheme S` (module
  `Langlands.AbelianScheme.GroupScheme`): group objects in schemes over
  `S`, and those with commutative multiplication. `A.toGrp` forgets
  commutativity. A morphism `g : T' ⟶ T` of commutative group schemes is a
  group-scheme homomorphism written additively, and
  `CommGroupScheme.groupHom g : T'.toGrp ⟶ T.toGrp` is that homomorphism.
  `GroupScheme.baseChange b` is pullback along `b : S' ⟶ S` with the
  induced group law.
- `SubgroupFunctor.range f` (module `Langlands.GroupScheme.SubgroupFunctor`):
  on each test scheme `U` over `S`, the subgroup of points `U ⟶ G` that
  factor through `f : H ⟶ G`. `SubgroupFunctor.comap f F` (module
  `Langlands.GroupScheme.Dynamic.Functoriality`): the points of `H` whose
  composite with `f` lies in `F`.
- `IsConnectedReductive` (module `Langlands.GroupScheme.Reductive.Basic`):
  smooth, affine, connected, with trivial unipotent radical after base
  change to an algebraic closure.
- `IsDerivedSubgroup d` (module `Langlands.GroupScheme.Derived.Basic`):
  `d` is a closed immersion whose range is the scheme-theoretic derived
  subgroup.
- `IsSimplyConnected C` (module `Langlands.GroupScheme.SimplyConnected.Basic`):
  `C` is semisimple, and every central isogeny onto `C` from a semisimple
  group is an isomorphism.
- `IsCentralIsogeny π` (module `Langlands.GroupScheme.CentralIsogeny.Basic`):
  `π` is an isogeny (finite, flat and surjective), locally of finite
  presentation, and its kernel is central.
- `IsSimplyConnectedDerivedCover dM πM` (module
  `Langlands.GroupScheme.SimplyConnected.DerivedCover`): `M` is connected
  reductive, `dM` is its derived subgroup, and `πM` is a simply connected
  central cover with the universal property `IsSimplyConnectedCover`.
- `IsSplitSubtorus a` (module `Langlands.GroupScheme.Rational.SplitTorus`):
  `A` is a split torus and `a` is a closed immersion.
- `(torusCentralizer a).IsRepresentedBy j` (modules
  `Langlands.GroupScheme.Rational.TorusCentralizer` and
  `Langlands.GroupScheme.SubgroupFunctor`): `j` is a monomorphism whose
  range is the centralizer functor of `a`, whose points over `U` are the
  points `g` of `G` such that, for every `V ⟶ U`, the restriction of `g`
  commutes with the image under `a` of every `V`-point of `A`. So
  `M = Z_G(A)`.
- `IsMaximalTorus t` (module `Langlands.GroupScheme.Torus.Maximal`): `T` is
  a torus, `t` is a closed immersion, and `t` is maximal among closed
  subtori.
- `rationalCharacters M` (module `Langlands.GroupScheme.Rational.Characters`)
  is the additive group of homomorphisms `M ⟶ 𝔾_m` over `k`, that is,
  `X^*(M)_k`. `characterRestrict p χ` is `p ≫ χ`.
- `IsSplitTorus` (module `Langlands.GroupScheme.Torus.Split`): isomorphic
  to a split torus on a finite index type.

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page = PDF page − 31.

Corollary 2.6.28 (printed pp. 105–106 / PDF pp. 136–137) reads: "Let `G`
be a connected reductive group, `M_0 ⊂ G` a minimal Levi subgroup. Then
`G(K)^0 ∩ M_0(k)^1 = M_0(k)^0`. Hence, `G(k)^0 ∩ M_0(k)^1 = M_0(k)^0`."
Here `k` is the valued field of §2.6 and `K` its maximal unramified
extension. Its proof (printed p. 106 / PDF p. 137) reduces to
`G(K)^♮ ∩ M_0(K)^1 ⊂ M_0(K)^0` and then says: "let
`M'_0` be the preimage of `M_0` in `G_sc`. Then the image of `M'_0(K)` is
`G(K)^♮ ∩ M_0(K)`. The kernel of the map `M'_0 → M_0` being finite, the
preimage of `M_0(K)^1` in `M'_0(K)` equals `M'_0(K)^1`, which by Lemma
2.6.27 equals `M'_0(K)^0`. Since `M'_0 → M_0` maps `M'_0(K)^0` to
`M_0(K)^0`, we conclude that `G(K)^♮ ∩ M_0(K)^1 ⊂ M_0(K)^0`."

The authors' list of corrections and additions (version of 1 November
2024, registered as `kaletha-prasad-2024-corrections`) has no entry for
Lemma 2.6.27 or Corollary 2.6.28. Its three §2.6 entries (PDF p. 25)
correct the formula for `ω_G` in §2.6(d), add before Definition 2.6.20
that `k` is Henselian with perfect residue field, and replace "reductive
group" by "reductive `k`-group" in Definition 2.6.23. The added assumption
concerns the valued field of §2.6, not this field-level statement.

The proposition is a derived formulation and not a numbered result of KP.
It isolates the group-theoretic facts that this proof uses without
comment, over an arbitrary field. In the corollary it is applied over
`K` to `G_K`, `M = (M_0)_K = Z_{G_K}(S_K)` and the maximal torus of the
data of Definition 2.6.23(1) for `M`:

- clauses 2 and 3 say that `M'` is the preimage of `M`, so a point of
  `G_sc(K)` mapping into `M(K)` is a point of `M'(K)`;
- clause 1 describes `M'` as the centralizer of a split torus in the
  simply connected group `C`, connected reductive. This is the setting in
  which the proof uses Lemma 2.6.27 ("Let `G` be simply connected and let
  `M_0 ⊂ G` be a minimal Levi subgroup. Then `M_0(K)^0 = M_0(K)^1`",
  printed p. 105 / PDF p. 136) for `M'_0` over `K`;
- clause 4 gives the step "the preimage of `M_0(K)^1` equals
  `M'_0(K)^1`", for the inclusion that the proof uses. If `v(χ(p(m))) = 1`
  for all `χ ∈ X^*(M)_K`, then `v(χ'(m))^n = 1` and so `v(χ'(m)) = 1` for
  every `χ' ∈ X^*(M')_K`;
- clauses 5 and 6 give the step "`M'_0 → M_0` maps `M'_0(K)^0` to
  `M_0(K)^0`" in the form needed for Definition 2.6.23(1). Derived points
  of `M'` map into the image of `M_sc(K)`. A maximal torus of `M'` maps
  into the given maximal torus `T` of `M`, and it splits over every field
  that splits `T`, so the same splitting field can be used for both tori.

The following standard argument is the provenance of the proposition. It
is not proved here. Write `f = π ≫ d : C → G`, which has finite central
kernel `ker π`.

- *Preimage.* Let `Z^0` be the maximal central torus of `G` (its
  radical), that is, the maximal subtorus of the scheme-theoretic centre
  `Z_G`, which is a group of multiplicative type. In general `Z^0` is not
  the identity component of `Z_G`. For `G = SL_p` in characteristic `p`,
  `Z_G = μ_p` has coordinate ring `k[t]/((t - 1)^p)`, so it is connected
  but not reduced, and hence not a torus, while `Z^0` is trivial. Then
  `G = Z^0 · D` with `Z^0 ∩ D` finite, and `Z^0 ⊆ M`, so also
  `M = Z^0 · (M ∩ D)`. The image of `A` in `G / Z^0 ≅ D / (D ∩ Z^0)` is
  a split torus; let `A_1` be the maximal subtorus of its preimage
  `(A · Z^0) ∩ D` in `D`, a group of multiplicative type. Then
  `A · Z^0 = A_1 · Z^0`, and since `Z^0` is central,
  `Z_G(A) ∩ D = Z_D(A_1)`. `A_1` is isogenous to the split image of `A`
  in `G / Z^0`. The preimage `π⁻¹(A_1)` lies in the preimage of a maximal
  torus of `D` containing `A_1`, which is a maximal torus of `C`, so it is
  of multiplicative type. Let `A'` be its maximal subtorus, a torus
  isogenous to `A_1`. A torus isogenous to a split torus is split, since
  its character lattice is torsion-free and the Galois action is trivial
  on its rationalization. So `A_1` and `A'` are split, and `A'` is a split
  subtorus of `C` with `π(A') = A_1`, hence `Z_C(A') ⊆ f⁻¹(M)`.
  Conversely, if a point `c` of `C` lies in `f⁻¹(M)`, the commutator map
  `A' → C`, `x ↦ c x c⁻¹ x⁻¹`, takes values in the central subgroup
  `ker π`, so it is a homomorphism from a torus to a finite group of
  multiplicative type. Such a homomorphism is trivial, so `c ∈ Z_C(A')`.
  This gives clauses 2 and 3. `M' = Z_C(A')` is connected reductive as
  the centralizer of a torus in the connected reductive group `C`
  (clause 1).
- *Characters.* `p : M' → M ∩ D` is surjective with finite central
  kernel `ker π ⊆ M'`. Since `M = Z^0 · (M ∩ D)` with `Z^0` central,
  `M_der` is also the derived subgroup of `M ∩ D`. So `p` induces an
  isogeny of cocentres `M'/M'_der → (M ∩ D)/M_der`, and `(M ∩ D)/M_der`
  is a subtorus of `M/M_der`. For a `k`-rational character `χ'` of `M'`, some multiple
  `n χ'` is the pullback of a character `ψ` of `(M ∩ D)/M_der`, which is
  Galois-invariant because pullback along an isogeny is injective and
  Galois-equivariant. Lift `ψ` to a character of `M/M_der` over `k^sep`
  and sum the lift over a finite Galois quotient through which the
  action factors. This gives a `k`-rational character of `M` restricting
  to `[Γ : Γ_0] · ψ`, which proves clause 4.
- *Derived subgroups.* `p` maps `M'_der` onto `M_der` with finite central
  kernel, so `M'_der → M_der` is a central isogeny. `M'_der` is simply
  connected (the derived formulation
  `SplitTorusCentralizerDerivedSimplyConnectedStatement`, KP proof of
  Lemma 2.6.27, printed p. 105 / PDF p. 136). The universal property of
  `πM` gives `e : CM → M'_der` over `M_der`. Since both `πM` and
  `M'_der → M_der` are central isogenies, `e` is a central isogeny from
  the semisimple group `CM` onto the simply connected group `M'_der`,
  hence an isomorphism. With `M'_der` represented by `d' : D' ⟶ M'`, the
  inverse of `e` is the lift `b : D' ⟶ CM` of clause 5.
- *Tori.* The torus `Z^0` is central in `M`, so `T · Z^0` is a torus
  containing `T`. By maximality `Z^0 ⊆ T`. Since `M = Z^0 · (M ∩ D)`, the
  map `M ∩ D → M / Z^0` is a central isogeny with kernel `Z^0 ∩ D`. Then
  `T ∩ D` is the preimage of the maximal torus `T / Z^0` under it, so it
  is a maximal torus of `M ∩ D`. Its preimage
  `T' = p⁻¹(T ∩ D)` under the central isogeny `M' → M ∩ D` is a maximal
  torus of `M'`, because `ker π` lies in every maximal torus. Let `g` be
  the restriction of `p` to `T'`. If `T_E` is split, so is its subtorus
  `(T ∩ D)_E`, and hence so is the isogenous torus `T'_E`. This gives
  clause 6.

This module supplies no proof. The proof is a separate obligation.
