# Proof that automorphisms of locally free rank-one sheaves are unique global units

`Langlands.AlgebraicGeometry.Picard.lineBundleAutomorphismScalar` (universe
parameter `u`) proves the published proposition
`Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarStatement.{u}`
from module `Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarStatement`,
which is imported unchanged. For every scheme `X : Scheme.{u}`, every module
sheaf `M : X.Modules` with `IsLocallyFreeRankOne M`, and every automorphism
`e : M ≅ M`, there is exactly one unit `r : Γ(X, ⊤)ˣ` with
`e.hom = scalarHom (r : Γ(X, ⊤)) (𝟙 M)`.

The proof adds no hypothesis. The scheme is arbitrary, including the empty
scheme, and the module sheaf is subject only to `IsLocallyFreeRankOne M`. No
case split is made: the empty scheme is handled by the same argument, because
its cover by trivializing opens is the empty cover of the empty space.

The module adds one helper lemma, faithfulness of the scalar action, and the
main theorem. Both reuse published results by their Lean names. The axioms used
are `propext`, `Classical.choice` and `Quot.sound`.

## Published inputs

- `Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof`): for
  `hM : IsLocallyFreeRankOne M` and any `φ : M ⟶ M` there is `c : Γ(X, ⊤)`
  with `φ = c • 𝟙 M`. It gives existence only.
- `Langlands.Scheme.Modules.smul_trivGen_injective` (same module): for a
  trivialization `t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf`
  and an inclusion `i : V ⟶ W`, if `a • trivGen t i = b • trivGen t i` for
  `a b : Γ(X, V)`, then `a = b`. Here `trivGen t i : Γ(M, V)` is the local
  generator of `M` over `V` given by the trivialization (module
  `Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation`).
- The action `c • f` of global functions on sheaf morphisms
  (`globalHomSMul` in `Langlands.AlgebraicGeometry.ModuleLinear`) is defined as
  `scalarHom c f`. On sections over an open `U` it multiplies by
  `restrictScalar U c`, the restriction of `c` to `U` (`global_smul_app`,
  which holds by `rfl`). The same module makes this action a module structure
  (`globalHomModule`) and composition bilinear (`globalSectionsLinear`).
- Mathlib's `TopCat.Sheaf.eq_of_locally_eq'` for the structure sheaf
  `X.sheaf`: two sections over an open that agree after restriction to each
  member of a cover of that open are equal.

## 1. Faithfulness: `smul_id_injective_of_isLocallyFreeRankOne`

`Langlands.Scheme.Modules.smul_id_injective_of_isLocallyFreeRankOne` states:
if `IsLocallyFreeRankOne M` and `a • 𝟙 M = b • 𝟙 M` for `a b : Γ(X, ⊤)`, then
`a = b`.

Proof. `choose` turns the hypothesis into, for every point `x`, an open
`W x` containing `x` and a proof `t x` that the type of trivializations
`M.restrict (W x).ι ≅ SheafOfModules.unit (W x).toScheme.ringCatSheaf` is
nonempty; `(t x).some` picks one. The opens `W x` cover
`⊤`, since each point lies in its own `W x`. By `eq_of_locally_eq'` applied to
`X.sheaf` with this cover, it suffices to show that `a` and `b` have the same
restriction to every `W x`. By `smul_trivGen_injective` for `(t x).some` and
the identity inclusion `𝟙 (W x)`, it suffices to show

`restrict(a) • g = restrict(b) • g`, where `g = trivGen (t x).some (𝟙 (W x))`.

This is the equation `a • 𝟙 M = b • 𝟙 M` evaluated on the section `g` over
`W x`: by `global_smul_app` the left side is `(a • 𝟙 M).app (W x) g` and the
right side is `(b • 𝟙 M).app (W x) g`, and the restriction
`restrictScalar (W x) a` is by definition the image of `a` under the structure
sheaf's restriction map along `W x ≤ ⊤`, which is the restriction used by
`eq_of_locally_eq'`. Lean accepts this step with `congrArg` and no rewriting.

This is the faithfulness argument suggested in the statement's Markdown: on a
trivializing open the generator plays the role of the section one of the
structure module, and separatedness of the structure sheaf finishes the proof.

## 2. The main theorem: `lineBundleAutomorphismScalar`

Fix `X`, `M`, `hM` and `e : M ≅ M`.

1. Existence of scalars. `exists_eq_smul_id_of_isLocallyFreeRankOne` applied
   to `e.hom` and to `e.inv` gives `c d : Γ(X, ⊤)` with `hc : e.hom = c • 𝟙 M`
   and `hd : e.inv = d • 𝟙 M`.
2. `c * d = 1`. By step 1 of this file it suffices to show
   `(c * d) • 𝟙 M = 1 • 𝟙 M`. The chain of equalities is
   `(c * d) • 𝟙 M = c • (𝟙 M ≫ (d • 𝟙 M))` (by `mul_smul` and `Category.id_comp`),
   `= e.hom ≫ e.inv` (by `hc`, `hd` and `Linear.smul_comp`, which moves the
   scalar `c` out of the left factor of a composite), and
   `= 1 • 𝟙 M` (by `e.hom_inv_id` and `one_smul`).
3. The unit. Since `Γ(X, ⊤)` is commutative, `d * c = 1` as well, and
   `r := ⟨c, d, c * d = 1, d * c = 1⟩ : Γ(X, ⊤)ˣ` is a unit with `(r : Γ(X, ⊤)) = c`.
4. Existence. `e.hom = scalarHom c (𝟙 M)` is `hc`, because `c • 𝟙 M` is
   `scalarHom c (𝟙 M)` by definition of the action.
5. Uniqueness. If `r'` is a unit with `e.hom = scalarHom (r' : Γ(X, ⊤)) (𝟙 M)`,
   then `(r' : Γ(X, ⊤)) • 𝟙 M = c • 𝟙 M` by combining this equation with `hc`.
   Step 1 of this file gives `(r' : Γ(X, ⊤)) = c = (r : Γ(X, ⊤))`, and
   `Units.ext` gives `r' = r`.

Faithfulness is used twice: to show that the scalar of `e.hom` is a unit, and
to show that the unit is unique.

## Relation to the literature

The statement's Markdown records its derived provenance from Edixhoven, van der
Geer and Moonen, *Abelian Varieties* (preliminary draft), Chapter VI §1,
paragraph (6.2), printed page 88 (PDF page 92). That passage uses, without
proof, the fact that an endomorphism of a line bundle is multiplication by a
global function. The present proof does not follow a source proof. It combines
the published Library existence theorem with the faithfulness argument above,
as described in the statement's proof leads.

## Authorship

Worker 317 wrote the Lean proof and this Markdown.
