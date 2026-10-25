# Epimorphic coefficient quotient units for sheaves

This is an internal categorical consequence of the existing coefficient quotient
construction in `Langlands.Sheaf.AdicSystem`. It is not a transcription of an
external source or a general exactness assertion.

Let `C : Type uC` have morphisms in universe `vC`, let `J` be a Grothendieck
topology on `C`, and let `R : Type u` be a commutative ring. Module carriers have
independent universe `v`. Assume `HasSheafify J (ModuleCat.{v} R)`. For any ideal
`I`, natural number `n` (including zero), and module sheaf `F`,
`quotientMap_app_epi` proves that the existing map

`F ⟶ (powers J I).obj (op n) |>.obj F`

is an epimorphism in the category of module sheaves. Here the target is the
sheafification of the presheaf of quotients `F(U) / I^n F(U)`; the notation
`I^n F(U)` means `(I^n) • ⊤` as a submodule.

The implemented proof first observes that each presheaf quotient map is
surjective, using `Submodule.mkQ_surjective` and
`ModuleCat.epi_iff_surjective`. `NatTrans.epi_of_epi_app` then proves that the
natural transformation of presheaves is an epimorphism. Sheafification, a left
adjoint, preserves epimorphisms. Finally, the defining formula for `quotientMap`
composes this sheafified morphism with the inverse sheafification counit, which
is an isomorphism on a sheaf. Composition preserves epimorphisms.

The assertion is categorical: it does not assert surjectivity on every module
of sections of the sheafification. No flatness, exactness of coefficient
reduction, completion comparison, or derived inverse-limit result is assumed or
proved here.
