# Noetherian approximation of a finite cover with quasi-affine quotient (Part II)

Module `Langlands.AlgebraicGeometry.QuasiAffineApproximation.Approximation`.

This is Part II of the proof of `QuasiAffineSourceAFNoetherianSchemeApproximationStatement`.
It proves `approximationInterface : ApproximationInterface.{u}`. The proposition
`ApproximationInterface` is defined in `QuasiAffineApproximation.Skeleton`. This is the
approximation in Gross, Proposition 3.5, Step 3 ("By approximating `X` and `p`, we may assume
that `X` is of finite type over `Z`"). The approximation runs on the étale presentation from
Part I, not on the algebraic space itself. The module is internal to the proof and has no
separate literature source. Its limit arguments use the published Library machinery for
cofiltered systems of étale equivalence relations and Stacks Project Lemma 32.5.3
(Tag 07RN), which is `AbsoluteNoetherianApproximation.exists_finiteTypeOpenModel_of_isLimit`.

## Declarations

- `schemeQuotientOfIsPullback`. Let `F` be an étale equivalence relation and `q : F.U ⟶ M`
  a flat, locally finitely presented, surjective morphism with kernel pair `(F.t, F.s)`. Then
  `M` with `q` is a `F.SchemeQuotient`. This needs `q` étale. Étaleness descends along the
  fpqc-type covering `q` from its base change `F.t`, which is étale
  (`MorphismProperty.of_isPullback_of_descendsAlong`).
- `exists_level_quasiAffine_quotient`. Let `D : I ⥤ EtaleEquivalenceRelation` be a cofiltered
  diagram whose object and relation schemes are affine. Assume every object scheme is
  locally of finite type over `Spec ℤ`. Let `c` be a cone over `D` whose image under the
  object functor is a limit cone. Suppose the limit relation `c.pt` has a scheme quotient
  `Qc` that is quasi-affine and whose quotient map is affine. Then some level `D.obj i` has a
  scheme quotient `Q` that is quasi-affine and whose quotient map is affine.
- `approximationInterface`. Let `(φ, g) : E' ⟶ E` be a cartesian morphism of étale
  equivalence relations with `E.U` affine and `φ` finite and surjective. Let `q : E'.U ⟶ M`
  be flat, locally finitely presented and surjective, with kernel pair `(E'.t, E'.s)` and `M`
  quasi-affine. Then there is a second such configuration `(φ₁, g₁) : E₁' ⟶ E₁`,
  `q₁ : E₁'.U ⟶ M₁` with:
  - `E₁.U` and `E₁.R` affine, and `φ₁` finite and surjective;
  - `M₁` quasi-affine and Noetherian;
  - maps `hV : E.U ⟶ E₁.U`, `hW : E'.U ⟶ E₁'.U` and `hM : M ⟶ M₁` with
    `hW ≫ φ₁ = φ ≫ hV` and `q ≫ hM = hW ≫ q₁`;
  - `hM` affine.

## Proof of `exists_level_quasiAffine_quotient`

1. Choose a finite affine open cover `W_k` of `Qc.M`. The preimages `Qc.q ⁻¹ W_k` form a
   finite invariant open cover of `c.pt.U`. Each preimage is affine, since `Qc.q` is affine,
   and each has an affine chart quotient (`hasAffineQuotient_chart`).
2. `CartesianDiagram.exists_invariantAffineQuotientCover` descends this cover to a level `i`.
   It gives an invariant affine open cover `V_k` of `(D.obj i).U` whose charts have affine
   quotients. Gluing these quotients gives a scheme quotient `Qi` of `D.obj i`
   (`schemeQuotientOfInvariantOpenCover`) with affine quotient map
   (`isAffineHom_q_of_invariantOpenCover`).
3. Restrict the diagram to the levels above `i` (`CartesianDiagram.above`). The object limit is
   preserved (`isLimitObjectAbove`). Each level `j ⟶ i` gets the quotient pulled back from `Qi`
   along the cartesian transition (`SchemeQuotient.ofIsCartesianHom`), and its quotient map
   is affine. The quotient functor `F` has affine transition maps
   (`SchemeQuotient.isAffineHom_map`). Its objects are quasi-compact and locally of finite
   type over `ℤ`. Its limit is `Qc.M` (`SchemeQuotient.isLimitQuotientCone`).
4. `Qc.M` is quasi-affine, so `Qc.M.toSpecΓ` is an open immersion into an affine scheme.
   `exists_finiteTypeOpenModel_of_isLimit` (Tag 07RN), with the empty set of functions,
   gives a level `j` and an open immersion of the quotient `(Q j).M` into some `Spec A`. A
   quasi-compact scheme with an immersion into an affine scheme is quasi-affine
   (`Scheme.IsQuasiAffine.of_isImmersion`).

## Proof of `approximationInterface`

1. *First level of finite type over `ℤ`.* `M` is separated, so `prod.lift E.t E.s` is a closed
   immersion (`isClosedImmersion_lift_of_separated_quotient` in
   `QuasiAffineApproximation.SeparatedQuotient`), and `E.R` is affine. The published
   tuple-tail induction (`nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems` together
   with `nonempty_finiteTypeCartesianSystem_tupleTailNext`) gives an affine first level `L` of
   `E` of finite type over `ℤ`. It comes with a cartesian morphism `h : E ⟶ L.relation`.
   Composing gives the cartesian morphism `hc : E' ⟶ L.relation`. The ring
   `Γ(L.relation.U, ⊤)` is Noetherian.
2. *Stable systems.* `h` and `hc` give cofiltered diagrams of stable finitely generated levels,
   `h.stableDiagram` and `hc.stableDiagram`, indexed by stable finitely generated
   `Γ(L.relation.U, ⊤)`-subalgebras of `Γ(E.U, ⊤)` and of `Γ(E'.U, ⊤)` respectively. Their
   levels are affine and locally of finite type over `ℤ` (`stableDiagram_locallyOfFiniteType`).
   Their stable cones have points `E` and `E'`. The object limit of `hc.stableDiagram` is
   `E'.U` (`stableCone_isLimitObject`).
3. *Quotient at a level of `E'`.* `q` is affine because `M` is separated and `E'.U` is affine.
   `schemeQuotientOfIsPullback` makes `q` a scheme quotient `Qc` of `E'`. By
   `exists_level_quasiAffine_quotient` applied to `hc.stableDiagram`, some level `i`,
   a subalgebra generated by a finite set `s`, has a quasi-affine quotient `Q` with affine
   quotient map.
4. *Finite surjective level pair.* On global sections, `φ` gives a finite map
   `ψ : Γ(E.U, ⊤) → Γ(E'.U, ⊤)`. It is equivariant for the two coactions
   (`IsCartesianHom.ringHom_comp_appTop`), and its map on spectra is surjective. So its kernel
   is nil, that is, contained in the nilradical of `Γ(E.U, ⊤)`
   (`RingEtaleGroupoid.ker_le_nilradical_of_comap_surjective`). The kernel need not be a
   nilpotent ideal, since `Γ(E.U, ⊤)` need not be Noetherian. Containment in the nilradical is
   exactly the kernel hypothesis of `RingEtaleGroupoid.exists_finite_level`, which then
   gives stable finitely generated subalgebras `D ⊆ Γ(E.U, ⊤)` and `D' ⊆ Γ(E'.U, ⊤)` with
   `s ⊆ D'` and a restriction `φD : D → D'` of `ψ`. The map `φD` is finite with surjective map
   on spectra. `D'` is finitely generated because it is finite over the finitely generated `D`.
   So `j := D'` is a level of `hc.stableDiagram` above `i`, and `jD := D` is a level of
   `h.stableDiagram`.
5. *The output.* Take `E₁ := h.stableDiagram.obj jD`, `E₁' := hc.stableDiagram.obj j` and
   `φ₁ := Spec φD`. The pair is cartesian by `RingEtaleGroupoid.isCartesianHom_of_equivariant`
   with `subalgebraCoaction_map`. `φ₁` is finite and surjective because `φD` is. Let `Q₁` be
   `Q` pulled back along the transition `j ⟶ i`, and set `M₁ := Q₁.M`, `q₁ := Q₁.q`. The map
   `Q₁.M ⟶ Q.M` is affine and `Q.M` is quasi-affine, so `M₁` is quasi-affine
   (`Scheme.IsQuasiAffine.of_isAffineHom`). It is quasi-compact and locally of finite type over
   `ℤ`, hence Noetherian. Let `hV` and `hW` be the stable cone legs at `jD` and `j`, and let
   `hM := SchemeQuotient.map` along the leg at `j`. This map is affine, and
   `q ≫ hM = hW ≫ q₁` by `SchemeQuotient.q_map`. The square `hW ≫ φ₁ = φ ≫ hV` reduces to
   `φD ≫ (D' ⊆ Γ(E'.U)) = (D ⊆ Γ(E.U)) ≫ φ.appTop` on rings, followed by naturality of
   `Scheme.isoSpec`.
