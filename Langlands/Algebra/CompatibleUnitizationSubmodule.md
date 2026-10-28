# Stable subspaces, restrictions and quotients of the unitized action

Author: Worker 734 read the cited passages, designed and implemented this module
and wrote this note. No draft code by another worker was reused. The module is
part 3 of task `2e6ba45d-844d-458a-aba5-3b706694aae6`. It imports two Library
modules by Lean name:

- `Langlands.Algebra.CompatibleUnitization` (parts 1, 2, 4 and 5 of the same
  task): `endHom`, `module`, `smul_eq`, `inr_smul`, `isScalarTower`,
  `zero_smul_eq`, `zero_inr_smul`;
- `Langlands.Algebra.CompatibleSubmodule` (task
  `225c0c50-f2f1-4da9-9cbd-b70bd64c5b33`, by Worker 277): `CompatibleSubmodule`,
  `CompatibleSubmodule.ofStable`, `toSubmodule`, `action_mem`, its complete
  lattice, `restrictAction`, `quotientAction` and `zeroOrderIso`.

The module `Langlands/Algebra/CompatibleUnitizationSubmodule.lean` (namespace
`Langlands.Algebra.CompatibleUnitization`) compares the stable `k`-subspaces of
an action `ρ : A →ₙₐ[k] Module.End k M` with the submodules of `M` for the
unitized action `module ρ`. It also compares the restricted and quotient
unitized actions with the unitizations of the restricted and quotient original
actions. Carriers, elements and the quotient map are unchanged throughout.

## Original source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**. This is the registered source
`renard-2026-representations-groupes-reductifs-padiques`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page = PDF page minus 6. Worker 734 read these passages directly:

- Chapter I, notation and conventions, printed pp. 5–6 / PDF pp. 11–12. Rings are
  not assumed unital, and modules over a unital ring are not assumed unital a
  priori.
- I.2.1, printed p. 14 / PDF p. 20. For a `ℂ`-algebra `A` without unit, Renard
  introduces `Ã = A ⊕ ℂ·1_A`. `A`-modules that are also `ℂ`-vector spaces
  "deviennent naturellement des Ã-modules unitaires".
- B.II, printed p. 272 / PDF p. 278. The proof of Schur's lemma replaces `A` by
  `Ã = A ⊕ ℂ1_A` "comme dans la section I.2.1", then uses that `ker f` and
  `Im f` are submodules of `M`. This module supplies the comparison of
  submodules and quotients that this reduction uses. Nothing from B.II itself is
  formalized.

Supplementary errata: the registered `renard-2010-corrections-complements`
(SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`).
PDF pp. 18–19 were checked. The item for the Schur lemma (2010 p. 314) asks that
`M` be a `ℂ`-vector space and that one reduce to `Ã` as in I.2.1. The 2026 text
already has this. The 2026 edition governs.

Provenance: every declaration here is **derived implementation content**. Renard
does not state the order isomorphism or the restricted and quotient comparisons.
He uses implicitly that a submodule of the `A`-module `M` that is also a
`ℂ`-subspace is an `Ã`-submodule, and conversely. The generalization from `ℂ` to
a commutative ring `k` is ours.

## Hypotheses, universes and action choices

Universes are independent: `k : Type u`, `A : Type v`, `M : Type w`. No space is
assumed finite-dimensional, nontrivial or nondegenerate. `A` is never assumed
commutative or unital, and `ρ` is arbitrary, including `0`. The general sections
assume

```text
[CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
[AddCommGroup M] [Module k M]
```

**Action selection.** As in `Langlands.Algebra.CompatibleUnitization`, the
unitized action `module ρ` is not an instance. Every statement installs it with
`letI := module ρ`. The restricted subspace `S.toSubmodule` carries
`module S.restrictAction`, and the quotient `M ⧸ S.toSubmodule` carries
`module S.quotientAction`, each installed with `letI`. A stable subspace is a
`CompatibleSubmodule ρ` (a `k`-submodule with `action_mem`), never an
arbitrary stable additive subgroup.

## 1. The order isomorphism

Section `OrderIso`; `ρ : A →ₙₐ[k] Module.End k M`.

- `toUnitizedSubmodule ρ S : Submodule (Unitization k A) M` has carrier
  `S.toSubmodule`. It is closed under the unitized action because
  `x • m = x.fst • m + ρ x.snd m` (`smul_eq`), and both terms lie in `S`
  (`smul_mem` and `S.action_mem`).
- `ofUnitizedSubmodule ρ p : CompatibleSubmodule ρ` is
  `CompatibleSubmodule.ofStable (p.restrictScalars k) _`, using the adapter
  `isScalarTower ρ`. Stability: `p.smul_mem (a : Unitization k A)` together with
  `inr_smul`.
- `submoduleOrderIso ρ : CompatibleSubmodule ρ ≃o Submodule (Unitization k A) M`
  bundles the two maps. Both round trips hold by extensionality on membership
  (`CompatibleSubmodule.ext` with `Iff.rfl`, and `rfl`). The order condition is
  `CompatibleSubmodule.toSubmodule_le_toSubmodule` followed by `Iff.rfl`.
- Membership: `mem_submoduleOrderIso` (`m ∈ submoduleOrderIso ρ S ↔ m ∈ S`)
  and `mem_submoduleOrderIso_symm`, both `Iff.rfl`.
- Unchanged carriers: `coe_submoduleOrderIso` (equal sets in `M`),
  `restrictScalars_submoduleOrderIso` (restricting scalars to `k` gives back
  `S.toSubmodule`), and `toSubmodule_submoduleOrderIso_symm` (the stable
  subspace of `p` is `p.restrictScalars k`).
- Round trips: `submoduleOrderIso_symm_apply_apply` and
  `submoduleOrderIso_apply_symm_apply`.
- Order and lattice laws, all from `OrderIso` lemmas: `submoduleOrderIso_le_iff`;
  `submoduleOrderIso_bot`, `submoduleOrderIso_top`, `submoduleOrderIso_symm_bot`,
  `submoduleOrderIso_symm_top` (`map_bot`, `map_top`); `submoduleOrderIso_inf`,
  `submoduleOrderIso_sup`, `submoduleOrderIso_sInf`, `submoduleOrderIso_sSup`,
  `submoduleOrderIso_iInf`, `submoduleOrderIso_iSup` (`map_inf`, `map_sup`,
  `map_sInf`, `map_sSup`, `map_iInf`, `map_iSup`). The lattice on the left is the
  complete lattice of `CompatibleSubmodule ρ`, and the lattice on the right is
  Mathlib's lattice of `Submodule (Unitization k A) M`.

## 2. Restricted actions

Section `Restrict`; `S : CompatibleSubmodule ρ`.

- `endHom_mem S x hm`: `endHom ρ x` maps `S` into itself, by `smul_mem` in
  `submoduleOrderIso ρ S`.
- `endHom_restrictAction S x`: `endHom S.restrictAction x` is the restriction
  `(endHom ρ x).restrict _` (`rfl`). So unitizing the restricted original action
  restricts the unitized action homomorphism.
- `restrictAction_smul_coe S x m`: under `module S.restrictAction`, the
  underlying element of `x • m` is `x • (m : M)` for `module ρ` (`rfl`).
- `restrictEquiv S : S.toSubmodule ≃ₗ[Unitization k A] submoduleOrderIso ρ S`,
  with `module S.restrictAction` on the left and the submodule action of
  `module ρ` on the right. It is the identity on elements, `m ↦ ⟨m, m.2⟩`. Every
  field, including `map_smul'`, is `rfl`.
- `coe_restrictEquiv_apply`, `coe_restrictEquiv_symm_apply`: same underlying
  elements of `M`. `subtype_restrictEquiv`: the unitized inclusion
  `(submoduleOrderIso ρ S).subtype` after `restrictEquiv S` is the `k`-linear
  inclusion `S.toSubmodule.subtype`.

## 3. Quotient actions

Section `Quotient`; `S : CompatibleSubmodule ρ`.

- `endHom_quotientAction S x`: `endHom S.quotientAction x` is
  `S.toSubmodule.mapQ S.toSubmodule (endHom ρ x) _`. Proof: extensionality on
  the quotient, then `rfl` on classes.
- `quotientAction_smul_mkQ S x m`: under `module S.quotientAction`,
  `x • S.toSubmodule.mkQ m = S.toSubmodule.mkQ (x • m)` with `module ρ` on the
  right (`rfl`).
- `quotientEquiv S : (M ⧸ S.toSubmodule) ≃ₗ[Unitization k A]
  M ⧸ submoduleOrderIso ρ S`, with `module S.quotientAction` on the left and
  Mathlib's quotient action of `module ρ` on the right. Its underlying
  `k`-linear equivalence is Mathlib's
  `Submodule.Quotient.restrictScalarsEquiv k (submoduleOrderIso ρ S)`, using
  `isScalarTower ρ`. Unitized linearity is checked on classes with
  `Submodule.Quotient.induction_on`, where it holds by `rfl`.
- `quotientEquiv_mkQ` and `quotientEquiv_symm_mkQ`: the class of `m` goes to
  the class of `m`, in both directions (`rfl`). So the comparison goes through
  the same quotient map.

## 4. The zero original action

Section `ZeroAction`, general hypotheses:

- `zeroSubmoduleOrderIso : Submodule k M ≃o Submodule (Unitization k A) M`,
  under `letI := module 0`. It is the composite of
  `(CompatibleSubmodule.zeroOrderIso).symm` with `submoduleOrderIso 0`: for the
  zero original action every `k`-subspace is a unitized submodule.
- `mem_zeroSubmoduleOrderIso`: same membership (`Iff.rfl`).

Section `Complex`, with `A = k = M = ℂ` and `ρ = 0 : ℂ →ₙₐ[ℂ] Module.End ℂ ℂ`.
Three `example`s check:

- `submoduleOrderIso 0 ⊥ = ⊥`, `submoduleOrderIso 0 ⊤ = ⊤`, and `⊥ ≠ ⊤` in
  `Submodule (Unitization ℂ ℂ) ℂ`. So the zero subspace is kept, and the lattice
  is nontrivial on the nonzero line;
- the quotient `ℂ ⧸ submoduleOrderIso 0 ⊤` is permitted and is a subsingleton
  (`Submodule.Quotient.subsingleton_iff`);
- on `⊤`, the unitization of the restricted zero action is `x • m = x.fst * m`
  on underlying elements, while `((1 : ℂ) : Unitization ℂ ℂ) • m = 0`. Proofs:
  `restrictAction_smul_coe` with `zero_smul_eq` and `zero_inr_smul`.

## 5. Field specialization

Section `Field`: a field `K`, a possibly noncommutative and nonunital
`K`-algebra `A` with `[IsScalarTower K A A] [SMulCommClass K A A]`, and a
`K`-vector space `V : Type w`. Three `example`s instantiate `submoduleOrderIso`,
`restrictEquiv` and `quotientEquiv` there.

## Deferred obligations

This module does not prove isomorphism theorems, exactness, simplicity
transfer, Schur, countable dimension, separation, finite generation or
localization. It does not identify stable `k`-subspaces with stable additive
subgroups. The tensor-product formula of I.2.1 and (I.2.1.2) are not claimed.
