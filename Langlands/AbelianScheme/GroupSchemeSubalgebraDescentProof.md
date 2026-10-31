# Proof of descent of group schemes to finitely generated subalgebras

`Langlands.GroupScheme.subalgebraDescent` proves `Langlands.GroupScheme.SubalgebraDescentStatement.{u}`
(module `Langlands.AbelianScheme.SubalgebraDescentStatements`) for an arbitrary universe `u`. See
`SubalgebraDescentStatements.md` for the statement and its sources.

This module contains no ported FLT code. It applies the ported FLT theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`
(module
`Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`,
Anthropic FLT Lean source at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache-2.0).
That theorem descends a group law on generalized points, FLT's `RelativeGroupLaw`, from Mathlib's chosen base change
`pullback.snd f₀ (Spec A ⟶ Spec A₀)` to a finitely generated stage `T`. The Library statement is about group objects
`G : GroupScheme (Spec A) = Grp (Over (Spec A))`, an arbitrary pullback square, and the functor
`GroupScheme.baseChange ψ = (Over.pullback ψ).mapGrp`. The bridge translates in both directions using FLT's
`relativeGroupLawOfGrpObj` and `RelativeGroupLaw.grpObjOverMk` (module
`Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj`).

## Helper lemmas

In a cartesian monoidal category `C`:

- `isMonHom_of_mul_comp`: let `M` be a monoid object and `N` a group object. If `f : M ⟶ N` satisfies
  `(x * y) ≫ f = (x ≫ f) * (y ≫ f)` for all generalized points `x y : X ⟶ M`, then `f` is a monoid morphism. `mul_hom`
  is the case `x = fst`, `y = snd` (via `MonObj.mul_eq_mul` and `MonObj.comp_mul`). `one_hom` follows from the case
  `x = y = 1`: it gives `1 ≫ f = (1 ≫ f) * (1 ≫ f)`, and cancellation in the group `𝟙_ C ⟶ N` gives `1 ≫ f = 1`.
- `isCommMonObj_of_iso`: commutativity of a monoid object is transported along an isomorphism `e : M ≅ N` whose `hom`
  is a monoid morphism. Every point of `N` has the form `a ≫ e.hom`, and `MonObj.mul_comp` moves the product to `M`.

For a morphism of schemes `ψ : S' ⟶ S`:

- `basePoint ψ z`: for `z : U ⟶ (Over.pullback ψ).obj Y`, the point `Over.mk (U.hom ≫ ψ) ⟶ Y` corresponding to `z`
  under the adjunction `Over.mapPullbackAdj ψ`. Its underlying morphism is `z.left ≫ pullback.fst Y.hom ψ`
  (`basePoint_left`, by `rfl`). Conversely, `homEquiv_left_fst` says that the adjunction bijection, followed by
  `pullback.fst`, recovers the underlying morphism.
- `mapPullbackAdj_homEquiv_mul`: for a group object `Y`, the adjunction bijection is multiplicative. It is the
  composite of the unit with `(Over.pullback ψ).map`, and `Functor.map_mul` and `MonObj.comp_mul` apply.
- `mul_left_fst`: for points `z₁ z₂` of `(Over.pullback ψ).obj Y` with its induced group structure,
  `(z₁ * z₂).left ≫ pullback.fst Y.hom ψ = (basePoint ψ z₁ * basePoint ψ z₂).left`. So the group law of the base
  change is read off from the group law of `Y`.

## The main proof

Fix the data of the statement: `f₀ : X₀ ⟶ Spec A₀`, the group scheme `G` over `Spec A`, `a : G.X.left ⟶ X₀` with
the pullback square `hP`, and `s : Finset A`.

1. **Transport to the chosen fibre product.** Let `p := pullback.snd f₀ (Spec A ⟶ Spec A₀)`. The square gives
   `eO : G.X ≅ Over.mk p` in `Over (Spec A)` (from `hP.isoPullback`). The group structure is transported by
   `GrpObj.ofIso eO`, so `eO.hom` is a monoid morphism (`isMonHom_ofIso`). Let `L := relativeGroupLawOfGrpObj A p`.
2. **Descent.** The FLT theorem applied to `f₀`, `L` and `s` gives: a finitely generated `T` containing `s`; a group
   law `Lₜ` on `pT := pullback.snd f₀ (Spec T ⟶ Spec A₀)`; an isomorphism `c` with `c ≫ pullback.snd = p`; the
   identity `hmul` saying that `c` carries `L.mul` to the multiplication of `Lₜ.baseChange ψ`, where
   `ψ := Spec A ⟶ Spec T`; and `hcomm : L.IsCommutative → Lₜ.IsCommutative`.
3. **The group scheme `G₀`.** `G₀ := Grp.mk (Over.mk pT)`, with the group structure `Lₜ.grpObjOverMk`. The witness
   `a₀` is `pullback.fst`, and the square is `IsPullback.of_hasPullback`.
4. **Commutativity.** If `G.X` is commutative, then so is `Over.mk p` (`isCommMonObj_of_iso eO`). Then `L` is
   commutative (`relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj`), so `Lₜ` is (`hcomm`), and `G₀.X` is commutative
   (`RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm`).
5. **The isomorphism.** `cO : Over.mk p ≅ ((GroupScheme.baseChange ψ).obj G₀).X` is `Over.isoMk (asIso c)`. The
   underlying object of the base change is `Over.mk (pullback.snd pT ψ)`, and `c ≫ pullback.snd = p` makes
   `Over.isoMk` applicable. The key step is that `cO.hom` is multiplicative on points `x y : X ⟶ Over.mk p`. By
   `Over.OverMorphism.ext` and `pullback.hom_ext` on `pullback pT ψ`, two equations are needed.
   - After `pullback.fst pT ψ`: the left side `(L.mul _ x y).1 ≫ c ≫ pullback.fst` is rewritten in a chain of steps.
     `hmul` turns it into the multiplication of `Lₜ.baseChange ψ`. `RelativeGroupLaw.baseChange_mul`,
     `baseChangePointOfBase_coe` and `pullback.lift_fst` turn that into `Lₜ.mul` at the points
     `baseChangePointToBase ψ (x ≫ c)`, `baseChangePointToBase ψ (y ≫ c)`. These points are, definitionally, the
     `basePoint`s of `x ≫ cO.hom` and `y ≫ cO.hom`. `RelativeGroupLaw.overHomToSchemeHomOver_mul` turns `Lₜ.mul` into
     the product of these `basePoint`s for the group structure `Lₜ.grpObjOverMk`. By `mul_left_fst`, that product is
     the right side `((x ≫ cO.hom) * (y ≫ cO.hom)).left ≫ pullback.fst`.
   - After `pullback.snd pT ψ`: both sides are morphisms over `Spec A` (`Over.w`).

   Let `Φ := eO ≪≫ cO`. Multiplicativity of `Φ.hom` follows from `MonObj.mul_comp` for the monoid morphism `eO.hom`
   and the multiplicativity of `cO.hom`. By `isMonHom_of_mul_comp`, `Φ.hom` is a monoid morphism, and
   `Grp.mkIso Φ` is the required isomorphism `G ≅ (GroupScheme.baseChange ψ).obj G₀`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound` (Lake-build inspection).
