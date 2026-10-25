# Sheafified scalar extension and etale restriction

This module constructs the natural comparison between sheafified coefficient
extension and restriction along an etale morphism. It proves compatibility with
the tensor-to-sheafification maps and the extension unit, and coherence for
identity and composite geometric maps.

## Scope and provenance

Let `R` and `S` be commutative rings in `Type u`, let `φ : R →+* S`, and let
`f : Y ⟶ X` be etale for schemes in `Scheme.{u}`. Module carriers also have
universe `u`. All sheaves here are ordinary module-valued sheaves on the actual
small etale sites. No flatness, injectivity, surjectivity or coefficient topology
is assumed.

This is an internal categorical construction, not a transcription of an external
theorem. It uses `EtaleScalarExtension` for tensor extension followed by
sheafification, `EtalePullback` for the continuous and cocontinuous composition
functor on etale objects, and `EtaleRestrictionRightAdjoint` for its pointwise
right Kan extension instances. The key Mathlib construction is
`Functor.pushforwardContinuousSheafificationCompatibility` in
`CategoryTheory/Sites/CoverLifting.lean`. Its equation
`Functor.toSheafify_pullbackSheafificationCompatibility` identifies the comparison
on the original presheaf. `CategoryTheory/Sites/Sheafification.lean` supplies
naturality and uniqueness of sheafification lifts.

Write `L_X` for `sheafExtendScalars φ X`, `T_X` for
`sheafRestrictScalars φ X`, and `P_f^R` for `restriction f (ModuleCat R)`.
Write `Q_X(F)` for the presheaf `F.obj ⋙ ModuleCat.extendScalars φ` and
`τ_X(F) : Q_X(F) ⟶ (L_X F).obj` for `tensorToSheafExtension φ X F`.
The notation `p_f` on presheaves means precomposition by `(siteMap f).op`.
Tensor postcomposition commutes definitionally with this precomposition.
Composition in the displayed equations follows Lean's order: `a ≫ b` means
first `a`, then `b`.

## The comparison and its tensor equations

`sheafExtendScalarsPullbackIso φ f` constructs a natural isomorphism

```text
β_f : L_X ⋙ P_f^S ≅ P_f^R ⋙ L_Y.
```

Mathlib's comparison has direction from the sheafification of the restricted
presheaf to the restriction of its sheafification. The implementation takes
its inverse and precomposes with the tensor-presheaf functor. Thus neither the
comparison nor its invertibility is an assumed input. The component
`β_f(F)` has source `P_f^S(L_X F)` and target `L_Y(P_f^R F)`.

`tensorToSheafExtension_pullback` proves

```text
p_f(τ_X(F)) ≫ β_f(F).hom = τ_Y(P_f^R F),
```

where the sheaf morphism is viewed as a presheaf morphism. Its proof composes
Mathlib's sheafification equation with the inverse comparison and cancels the
isomorphism. `tensorToSheafExtension_pullback_inv` gives the reverse equation

```text
τ_Y(P_f^R F) ≫ β_f(F).inv = p_f(τ_X(F)).
```

This is Mathlib's original equation with the project's definitions instantiated.

`sheafExtensionUnit_pullback` proves that, for the extension-adjunction unit
`η_X : Id ⟶ L_X ⋙ T_X`,

```text
P_f^R(η_X(F)) ≫ T_Y(β_f(F).hom) = η_Y(P_f^R F).
```

The source of the second arrow is identified using the definitional commutation
of scalar restriction and geometric restriction. On a section `m`, the unit
is the image of `1 ⊗ m`; the proof evaluates the tensor comparison equation on
that element.

## Uniqueness and naturality tools

`sheafExtensionPullback_hom_ext` says that two sheaf morphisms from
`P_f^S(L_X F)` to an `S`-module sheaf `E` are equal if they agree after
precomposition with `p_f(τ_X(F))`. The proof first precomposes with `β_f(F).inv`,
uses `sheafify_hom_ext` and the inverse tensor equation, and then cancels by
composing with `β_f(F).hom`.

`tensorToSheafExtension_naturality` specializes sheafification naturality to a
morphism `a : F ⟶ F'` of `R`-module sheaves:

```text
τ_X(F) ≫ L_X(a).hom = Q_X(a) ≫ τ_X(F').
```

## Geometric identity and composition coherence

Let `i_X^R : P_id^R ≅ Id` denote the published `restrictionId`. The theorem
`sheafExtendScalarsPullbackIso_id` proves the component equation

```text
β_id(F).hom ≫ L_X(i_X^R(F).hom) = i_X^S(L_X F).hom.
```

The proof reduces equality to the restricted tensor presheaf, applies the tensor
comparison and naturality equations, and uses naturality of `τ_X(F)` along the
site isomorphism defining `restrictionId`.

Now let `g : Z ⟶ Y` also be etale and write
`c_(f,g)^R : P_f^R ⋙ P_g^R ≅ P_(g ≫ f)^R` for `restrictionComp f (ModuleCat R) g`.
`tensorToSheafExtension_restrictionComp_inv` is the auxiliary naturality square

```text
p_(g ≫ f)(τ_X(F)) ≫ c_(f,g)^S(L_X F).inv
  = Q_Z(c_(f,g)^R(F).inv) ≫ p_g(p_f(τ_X(F))).
```

Its proof is naturality of `τ_X(F)` along the site comparison for composition.
`sheafExtendScalarsPullbackIso_comp` then proves

```text
β_(g ≫ f)(F).hom ≫ L_Z(c_(f,g)^R(F).inv)
  = c_(f,g)^S(L_X F).inv ≫ P_g^S(β_f(F).hom) ≫ β_g(P_f^R F).hom.
```

Both sides go from `P_(g ≫ f)^S(L_X F)` to `L_Z(P_g^R(P_f^R F))`. The proof
uses the morphism-extensionality result, rewrites the tensor maps with the
comparison equations, and applies the auxiliary naturality square. The final
identification is the definition of functor composition on objects.

## Remaining scope

The comparison concerns etale scheme morphisms and ordinary sheaves. This module
does not yet lift scalar extension to equivariant sheaves, prove mixed coherence
with composition of ring homomorphisms, or construct coefficient diagrams,
ideal reductions or inverse systems. It makes no claim about exactness,
preservation of injectives, global sections, higher cohomology, compact supports
or smooth actions. Those constructions and the required Harris specialization
remain separate work.
