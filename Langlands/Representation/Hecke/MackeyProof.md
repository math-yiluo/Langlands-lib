# Proof of Renard's two Mackey natural isomorphisms

Worker 231, Task 5449.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.11 Theorem and proof displays
(III.2.11.1)–(III.2.11.10), printed pp.82–83 / PDF pp.88–89; registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The theorem `Langlands.Hecke.Homomorphism.mackeyIsomorphismStatements` proves the
exact published target `Langlands.Hecke.Homomorphism.MackeyIsomorphismStatements`,
with independent universes `uG`, `uH`, `v` and carrier universe `max uG v`.

`smoothCurrying G` repackages the published categorical smooth currying
`smoothCurry` (Renard III.1.15, module `MackeyCurrying`) as a
`Mackey.Currying (smoothTensorBifunctor G) (smoothHomBifunctor G)`. Its combined
naturality equation is checked on underlying linear maps, where both sides agree
definitionally.

## Proof

The published `smoothInductionAdjunctionStatement` (Renard III.2.1) supplies:

- the equivalence proofs `eG` and `eH`;
- a natural isomorphism `iso : restriction φ hφ ≅ smoothF`;
- adjunctions `smoothF ⊣ smoothI` and `smoothP ⊣ smoothPseudoF`.

The equivalences and `iso` are returned as the first three conclusions.

**Hom isomorphism.** Transporting the first adjunction along `iso.symm` gives
`restriction φ hφ ⊣ smoothI`. Restriction commutes with the actual diagonal
tensor by the identity, so `μ` is `Iso.refl _`; this is (III.2.11.3). The abstract
`Mackey.homMackeyIso` then yields `mackeyHomLeft ≅ mackeyHomRight`, natural in both
variables, through displays (III.2.11.1)–(III.2.11.5).

**Tensor isomorphism.** The hypothesis `prem : smoothPseudoF ≅ smoothF` transports
the second adjunction along `prem ≪≫ iso.symm` to `adj : smoothP ⊣ restriction φ hφ`.
This step works for any such isomorphism, whether or not it is canonical. The
source leaves step (III.2.11.8) unjustified. Here
`exists_openSubgroup_le_map_of_adjunction` (module `MackeyOpenness`) shows that
`adj` forces each `φ(U)`, for `U` an open subgroup of `H`, to contain an open
subgroup of `G`. With that condition, `restrictionHomIso` identifies the
restricted smooth Hom with the smooth Hom of the restrictions. This identification
is (III.2.11.8). The abstract `Mackey.tensorMackeyIso` then yields
`mackeyTensorLeft ≅ mackeyTensorRight`, natural in both variables, through displays
(III.2.11.6)–(III.2.11.10).

The source writes the tensor factors as `V ⊗ P(W)` and `P(F(V) ⊗ W)`. The Lean
target and this proof use `P(W) ⊗ V` and `P(W ⊗ Fφ(V))`, as fixed by the published
statement.

## Helper modules

- `Langlands.Representation.Hecke.MackeyYoneda`: the abstract currying datum and
  the two abstract Mackey isomorphisms.
- `Langlands.Representation.Hecke.MackeyOpenness`: the openness lemma and the
  comparison `restrictionHomIso`.
