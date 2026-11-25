/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportBase
import WeilConjectures.AlgebraicGeometry.RightAdjointMateSchemeIsoTransportMate

/-! # Transport of a right-adjoint mate across a scheme isomorphism

Source: Stacks Project, Duality for Schemes, Tag 0ATR.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Transport both ordinary base change and its right-adjoint mate when the source
scheme of the vertical morphism is replaced by an isomorphic scheme.
Source: Stacks Project, Duality for Schemes, Tag 0ATR, Lemma 48.5.2,
and Tag 0E9S, invariance under the cartesian restriction identification.
(blueprint: lem-sc-right-adjoint-mate-scheme-iso-transport)

Proof: The projection equations identify r with the pullback of e.hom, hence r is
an isomorphism. Derived pullback along e.hom and along r are equivalences; their
inverse functors are pullback along the inverse scheme maps, with the composition
and identity comparisons. Derived direct-image composition identifies the two
vertical direct images under these equivalences. Uniqueness of right adjoints,
with its unit and counit identities, identifies a with b and d with b'.
Ordinary base change is natural under this identification: transpose under the
pullback/direct-image adjunction, use the two projection equations and the
associativity of pullback composition, then use injectivity of the Hom equivalence.
Thus the ordinary base-change component for f is a conjugate of the component
for f' at the equivalent object, and is invertible. In the formula for the second
mate, move the units and counits across these adjunction comparisons. ConjugateEquiv
preserves the conjugated ordinary comparison and its inverse. The resulting square
commutes and has invertible vertical sides, giving the asserted arrow isomorphism.
No invertibility of either right-adjoint mate is required. Empty schemes and zero
objects satisfy the same naturality and triangle identities. -/
theorem rightAdjoint_mate_scheme_iso_transport
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {P U S T : Scheme.{u}}
    [CompactSpace P] [QuasiSeparatedSpace P] [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace T] [QuasiSeparatedSpace T]
    (f : P ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : U ⟶ S) [QuasiCompact f'] [QuasiSeparated f']
    (e : U ≅ P) (he : e.hom ≫ f = f') (g : T ⟶ S)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory P)
    (b : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory U)
    (d : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f g))
    (b' : schemeDerivedQCohCategory T ⥤ schemeDerivedQCohCategory (pullback f' g))
    (adja : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f _ _).fst E.obj E.property) ⊣ a)
    (adjb : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty U).ι ⋙ schemeDerivedDirectImage f')
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _
        f' _ _).fst E.obj E.property) ⊣ b)
    (adjd : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ d)
    (adjb' : (schemeDerivedQCohProperty T).lift
      ((schemeDerivedQCohProperty (pullback f' g)).ι ⋙ schemeDerivedDirectImage (pullback.snd f' g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f' g)) _ _ _ _
        (pullback.snd f' g) _ _).fst E.obj E.property) ⊣ b')
    (hβ : ∀ E : schemeDerivedQCohCategory U,
      IsIso (schemeDerivedBaseChangeMap f' (pullback.snd f' g) g
        (pullback.fst f' g) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory S)
    (r : pullback f' g ⟶ pullback f g)
    (hr₁ : r ≫ pullback.fst f g = pullback.fst f' g ≫ e.hom)
    (hr₂ : r ≫ pullback.snd f g = pullback.snd f' g) :
    (∀ E : schemeDerivedQCohCategory P,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj)) ∧
    (∀ hβf : ∀ E : schemeDerivedQCohCategory P,
        IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition E.obj),
      Nonempty (Arrow.mk ((derivedPullback r).map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
      (dualityEquationBaseChangeMap f g a d adja adjd hβf K))) ≅
        Arrow.mk ((schemeDerivedQCohProperty (pullback f' g)).ι.map
      (dualityEquationBaseChangeMap f' g b b' adjb adjb' hβ K)))) := by
  have hbase :=
    rightAdjoint_mate_scheme_iso_transport_base f f' e he g hβ r hr₁ hr₂
  refine ⟨hbase, ?_⟩
  exact
    rightAdjoint_mate_scheme_iso_transport_mate f f' e he g a b d b'
      adja adjb adjd adjb' hβ K r hr₁ hr₂

end AlgebraicGeometry
