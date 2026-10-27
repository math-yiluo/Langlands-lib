# Intrinsic scalar of kernel translation

Let `f : A ⟶ B` be an actual homomorphism of abelian schemes over an arbitrary
scheme `S`. Fix `T` over `S`, a module sheaf `M` on `T ×_S B`, and an actual
trivialization `α : f_T^* M ≅ O_(T ×_S A)`. In particular `M` can be the
underlying module of an actual line bundle. No local freeness hypothesis is
needed for this scalar construction.

For `a : U ⟶ T` and a point `k : U ⟶ ker(f)`, let `q` be the ordinary map
`U ×_S A → T ×_S A` and let `r = kernelShear f a k` be the map
`(u,x) ↦ (a(u),k(u)+x)`. The published kernel calculation gives
`q ≫ f_T = r ≫ f_T`. The canonical equal-composite comparison `C` is formed
from actual module-pullback composition isomorphisms and pullback along that
equality. With `ι_q : q^* O ≅ O` and `ι_r : r^* O ≅ O`,
`kernelTranslationAut f α a k` is the composite

`ι_q⁻¹ ; (q^*α)⁻¹ ; C ; r^*α ; ι_r`.

Composition here is written in execution order. Thus the translated
trivialization follows the inverse ordinary trivialization. This is the
transported action divided by the trivial action, in the orientation of EGM
VII §7.3, rather than its inverse.

`kernelTranslationScalar` is the automorphism's global value at one, an actual
global unit on `U ×_S A`. Its action on every local section is multiplication
by the restriction of that global unit, by `structureAutScalar_hom_app`.
`kernelTranslationUnit f α h a k` is its unique preimage in `Γ(U,O_U)^×`
under the actual projection on units. The explicit proposition
`h : UniversalGlobalFunctions A` says that the actual structure morphism
induces an isomorphism on global functions after every base change. The
published `universalGlobalFunctions A` proves this for abelian schemes.
`relativeUnitsPullback_kernelTranslationUnit` is the evaluation formula
`π_U^* ν_α(a,k) = kernelTranslationScalar f α a k`.

The unit point gives the identity automorphism and unit. The three `_precomp`
lemmas prove naturality along any further parameter map `b : V ⟶ U`:
`ν_α(b ≫ a,b ≫ k) = b^*ν_α(a,k)`.
`kernelTranslationAut_mul` proves the translation cocycle by applying the
published comparison cocycle and its precomposition law. Pullback by a kernel
translation has the same effect as the identity on base-derived units;
`relativeUnitDescend_map` therefore turns that cocycle into
`kernelTranslationUnit_mul`:
`ν_α(a,k*l) = ν_α(a,k) * ν_α(a,l)`.

This is a complete progressive scalar unit, internally derived from
`EqualCompositePullback`, `StructureUnitScalars`, `KernelTranslationFamily`
and `RelativeGlobalUnits`. Its motivating original is Edixhoven–van der
Geer–Moonen, *Abelian Varieties*, preliminary build 2012-02-08,
VII §§7.1–7.4, printed pp.98–100 / PDF pp.102–104. The source defines a
left action by a comparison from ordinary pullback to translated pullback,
extracts its scalar relative to the trivial action, and uses universal
constant functions to turn the cocycle into a homomorphism. This file gives
that forward scalar construction without quotient, freeness, finiteness or
faithful flatness hypotheses. It does not yet package a scheme character,
prove independence of the trivialization, or assert effective descent,
representability, perfectness or Cartier duality.
