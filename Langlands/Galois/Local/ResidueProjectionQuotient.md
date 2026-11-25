# The residue projection of a separable closure: the quotient by inertia

`Langlands.Galois.Local.ResidueProjectionQuotient` proves the twenty-first clause of
`ResidueProjectionProperties K Ω` (`Galois/Local/ResidueProjectionStatement.lean`): the
quotient of the Galois group of a separable closure by inertia is isomorphic, as a
topological group, to the absolute Galois group of the residue field, through the residue
homomorphism. The clause asks for the existence of such an isomorphism; this file gives it
as a definition, `SepClosed.absoluteResidueQuotientEquiv`, with its value on classes.

## Setting

Both declarations take, as the statement does,

```lean
(K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
(Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
```

in independent universes, with local instances specific to this module for
`Algebra.IsAlgebraic K Ω`, the local norm of `K` and finiteness of the residue field of its
unit ball, as in `ResidueProjectionInertia.md`. Notation as there: `G = Ω ≃ₐ[K] Ω`,
`I = absoluteInertia K Ω`, `ρ = absoluteResidueHom K Ω`.

## Statements

**`SepClosed.absoluteResidueQuotientEquiv`** (definition). The isomorphism of topological
groups between `G/I`, with the quotient topology, and `Field.absoluteGaloisGroup 𝓀[K]`,
with the Krull topology:

```lean
def Langlands.LocalGalois.SepClosed.absoluteResidueQuotientEquiv
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] :
    ((Ω ≃ₐ[K] Ω) ⧸ absoluteInertia K Ω) ≃ₜ* Field.absoluteGaloisGroup 𝓀[K]
```

**`SepClosed.absoluteResidueQuotientEquiv_apply`** (clause 21 with the previous
definition). It sends the class of `σ` to `ρ σ`:

```lean
theorem Langlands.LocalGalois.SepClosed.absoluteResidueQuotientEquiv_apply
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (σ : Ω ≃ₐ[K] Ω) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    absoluteResidueQuotientEquiv K Ω (QuotientGroup.mk σ) = absoluteResidueHom K Ω σ
```

## Proofs

The definition is the composite of two isomorphisms of topological groups:

1. the Library's `residueQuotientEquiv K Ω : (G ⧸ inertia K Ω) ≃ₜ* Gal(k_B/k_A)`
   (`Galois/Local/SpectralProof.lean`, for `L/K` Galois with finite residue field of the
   base; here `IsGalois K Ω` is Mathlib's `IsSepClosure.isGalois`). It is the first
   isomorphism theorem for the surjective homomorphism `residueHom K Ω`, continuous by the
   universal property of the quotient topology, with continuous inverse because `G/I` is
   compact and `Gal(k_B/k_A)` Hausdorff. Since `absoluteInertia K Ω` is by definition
   `inertia K Ω`, its source is `G/I`;
2. `residueTransportEquiv K Ω : Gal(k_B/k_A) ≃ₜ* Field.absoluteGaloisGroup 𝓀[K]`
   (`ResidueProjectionInertia.md`).

On the class of `σ` the first sends it to `residueHom K Ω σ` and the second applies
`residueTransport K Ω`; the composite is `ρ σ` by definition of `absoluteResidueHom`, so
`absoluteResidueQuotientEquiv_apply` holds by `rfl`.

## Declarations, in order

1. `rpQuotientIsAlgebraic`, `rpQuotientNormedField`, `rpQuotientUltrametric`,
   `rpQuotientComplete`, `rpQuotientResidueFinite` (local instances, namespace
   `Langlands.LocalGalois.SepClosed`).
2. `SepClosed.absoluteResidueQuotientEquiv` (definition).
3. `SepClosed.absoluteResidueQuotientEquiv_apply` (theorem; clause 21).

## Literature

- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), file
  `/srv/central-library/Serre--Local Fields--1979.pdf` (SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`): Chapter I, §7,
  Proposition 20, printed p. 21 (finite case: `D/T ≅ G(l/k)`); Chapter III, §5,
  Corollary 1 to Theorem 3, printed pp. 54–55 (`G(K_nr/K) = G(k_s/k)`, and for a finite
  residue field `G(k_s/k)` is isomorphic to `Ẑ`). Serre identifies the Galois group of the
  maximal unramified extension, which is `G/I`, with that of `k_s/k`; for `k` finite,
  `k_s` is an algebraic closure. The topological statement is not made there.
- Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), file
  `/srv/central-library/Neukirch--Algebraic number theory (book)--1999.pdf` (SHA-256
  `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`): Chapter II, §9,
  Proposition (9.9), printed p. 172 (the exact sequence `1 → I_w → G_w → G(λ|κ) → 1` for an
  infinite Galois extension) and printed p. 173 (Definition (9.10), the isomorphism
  `G(T_w|Z_w) ≅ G(λ|κ)`, and, for `K` henselian and its separable closure,
  `G(T|K) ≅ G(κ̄_s|κ)` with `T = K_nr`). Over a complete `K`, `G_w` is the whole group.
- J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Thompson / Academic
  Press (1967), file
  `/srv/central-library/Cassels-Frohlich--Algebraic Number Theory--1967/Cassels-Frohlich--Algebraic Number Theory--1967.pdf`
  (SHA-256 `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`): Chapter I
  (A. Fröhlich, "Local Fields"), §7, Corollary 2, printed p. 28: the Galois group
  `Γ(K_nr/K)` is isomorphic *as a topological group* with the Galois group `Γ(k^s/k)` of
  the separable closure of the residue field; and the Application on the same page: for
  `k` finite with `q` elements, `Ẑ ≅ Γ(K_nr/K)` as topological groups via the Frobenius
  substitution. Here the statement is for `G/I` rather than `Γ(K_nr/K)`, which is the
  same group once `K_nr` is identified with the fixed field of `I`; the Library's
  statement does not mention `K_nr`.
