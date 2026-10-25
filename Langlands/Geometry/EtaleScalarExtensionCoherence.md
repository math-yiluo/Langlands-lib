# Identity and composition for sheafified scalar extension

The namespace is `Langlands.Geometry.EtaleCohomologyAction`. This module
constructs canonical identity and composition isomorphisms for ordinary
coefficient-sheaf extension on a fixed scheme. It proves their compatibility
with the adjunction units and their two identity laws and associativity law.

## Parameters and provenance

The parameters are arbitrary commutative rings `R A B C : Type u`, ring maps
`φ : R →+* A`, `ψ : A →+* B`, `χ : B →+* C`, and `X : Scheme.{u}`.
Module carriers also lie in `Type u`. The category at a coefficient ring R is
`EtaleDerivedSections.ModuleSheaf X R`, the category of R-module sheaves on
`X.smallEtaleTopology`. No flatness, injectivity, surjectivity, or topology on
the coefficient rings is assumed.

This is an internal categorical construction. It uses the published
`EtaleScalarExtension` functor and adjunction and the ordinary-sheaf restriction
isomorphisms from `EtaleScalarCoherence`. Its additional input is Mathlib's
`CategoryTheory/Adjunction/Mates.lean`, specifically `conjugateIsoEquiv` and the
conjugation identities for units, composition, whiskering, associators and
unitors. No external theorem is transcribed and no comparison map or coherence
law is supplied as an assumption.

Write L_φ for `sheafExtendScalars φ X`, T_φ for
`sheafRestrictScalars φ X`, and η_φ for `sheafExtensionUnit φ X`.
Thus L_φ is sectionwise tensor extension followed by sheafification, and the
constructed adjunction is L_φ ⊣ T_φ. Write

\[
 j_R:T_{\mathrm{id}_R}\xrightarrow{\sim}\mathrm{Id},\qquad
 d_{\varphi,\psi}:T_{\psi\circ\varphi}\xrightarrow{\sim}T_\psi\mathbin{\ggg}T_\varphi
\]

for the previously constructed restriction comparisons. Here `⋙`, written
\(\ggg\) in formulas, applies the left functor first; a semicolon similarly
composes morphisms in order of application.

## Constructed comparisons

`sheafExtendScalarsIdIso` constructs

\[
 i_R:L_{\mathrm{id}_R}\xrightarrow{\sim}\mathrm{Id}.
\]

It is the inverse image of j_R⁻¹ under `conjugateIsoEquiv` for the identity
adjunction and L_id ⊣ T_id. `sheafExtendScalarsCompIso` constructs

\[
 c_{\varphi,\psi}:L_{\psi\circ\varphi}
   \xrightarrow{\sim}L_\varphi\mathbin{\ggg}L_\psi.
\]

It is the inverse image of d_φ,ψ⁻¹ under the same equivalence for the composite
adjunction `(adj φ).comp (adj ψ)` and `adj (ψ.comp φ)`.
These constructions include natural inverse maps and both inverse identities.
The lemmas `conjugate_sheafExtendScalarsIdIso_hom` and
`conjugate_sheafExtendScalarsCompIso_hom` identify their conjugates exactly as
j_R⁻¹ and d_φ,ψ⁻¹. Both proofs are inverse laws of the conjugation equivalence.

## Compatibility with units

For an R-module sheaf F, `sheafExtensionUnit_id` proves

\[
 (\eta_{\mathrm{id}_R})_F\ ;\ T_{\mathrm{id}_R}((i_R)_F)
   =(j_R^{-1})_F.
\]

`sheafExtensionUnit_comp` proves

\[
 (\eta_{\psi\circ\varphi})_F\ ;\ T_{\psi\circ\varphi}((c_{\varphi,\psi})_F)
 = (\eta_\varphi)_F\ ;\ T_\varphi((\eta_\psi)_{L_\varphi F})
     \ ;\ (d_{\varphi,\psi}^{-1})_{L_\psi(L_\varphi F)}.
\]

Both equations are obtained from `unit_conjugateEquiv`, using the preceding
conjugate identities; the second also expands the unit of a composite
adjunction. The displayed i and c maps are their forward components.

## Identity and associativity coherence

`sheafExtendScalarsCompIso_id_left` splits L_φ using
c_id_R,φ, applies L_φ to the identity comparison i_R, and removes the resulting
identity functor by the left unitor. The composite is the identity of L_φ.

`sheafExtendScalarsCompIso_id_right` splits L_φ using
c_φ,id_A, evaluates i_A after L_φ, and removes the identity functor by the
right unitor. This composite is again the identity of L_φ.

`sheafExtendScalarsCompIso_assoc` proves equality of the following two
natural transformations from L_χ∘ψ∘φ to
L_φ ⋙ (L_ψ ⋙ L_χ):

- Split by c_ψ∘φ,χ, apply L_χ to c_φ,ψ, and then apply the functor associator.
- Split by c_φ,χ∘ψ and then evaluate c_ψ,χ after L_φ.

These proofs apply injectivity of `conjugateEquiv`. The conjugation formulas
for composition, whiskering, the unitors and the associator reduce each goal
to an equation between restriction comparisons. The identity proofs explicitly
present the conjugate with the composite ring-map adjunction; the associativity
proof normalizes `RingHom.comp_assoc`. Finally, extensionality at a sheaf F,
an etale object U and a section x proves the restriction equation by reflexivity:
all constituent restriction comparison maps leave the section element unchanged.
The proof does not assume that tensor presheaves are already sheaves.

## Scope

This unit concerns ordinary sheaves on one fixed scheme and coefficient-ring
identity/composition. Geometric pullback compatibility and equivariance,
varying-scheme diagrams, ideal reduction, inverse systems, derived scalar
comparisons, compact supports, smoothness and Harris specialization remain
separate obligations. No exactness, preservation of injectives, or commutation
with global sections or higher cohomology is asserted.
