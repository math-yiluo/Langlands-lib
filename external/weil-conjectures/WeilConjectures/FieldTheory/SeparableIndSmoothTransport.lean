/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.FieldTheory.SeparableSmoothColimit
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.RingHom.Smooth

/-! # Ind-smoothness transported from a separable field extension

Source: Stacks Project, Algebra, Lemma 07BV; Smoothing Ring Maps,
Lemma 07FE (lemma-resolve-special), final residue-field argument.
(blueprint: lem-weil-pbc-separable-ind-smooth-transport).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
private noncomputable def algebraIsColimitOfForget
    {R : Type u} [CommRing R] {I : Type v} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{v} R} {c : Limits.Cocone F}
    (ht : Limits.IsColimit ((forget (CommAlgCat.{v} R)).mapCocone c)) : Limits.IsColimit c := by
  classical
  let U := forget₂ (CommAlgCat.{v} R) CommRingCat.{v}
  letI : Limits.ReflectsColimitsOfShape I (forget CommRingCat.{v}) :=
    Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc : Limits.IsColimit (U.mapCocone c) :=
    Limits.isColimitOfReflects (forget CommRingCat.{v}) ht
  let i : I := Classical.choice IsFiltered.nonempty
  refine
    { desc := fun s ↦ CommAlgCat.ofHom
        { __ := (hc.desc (U.mapCocone s)).hom
          commutes' := ?_ }
      fac := ?_
      uniq := ?_ }
  · intro r
    have h := ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) i)
      (algebraMap R (F.obj i) r)
    change (hc.desc (U.mapCocone s)).hom
      ((c.ι.app i).hom (algebraMap R (F.obj i) r)) =
      (s.ι.app i).hom (algebraMap R (F.obj i) r) at h
    simp only [AlgHom.commutes] at h
    exact h
  · intro s j
    ext x
    exact ConcreteCategory.congr_hom (hc.fac (U.mapCocone s) j) x
  · intro s m hm
    have h : U.map m = hc.desc (U.mapCocone s) := by
      apply hc.hom_ext
      intro j
      exact (congrArg (fun f ↦ U.map f) (hm j)).trans (hc.fac (U.mapCocone s) j).symm
    ext x
    exact ConcreteCategory.congr_hom h x

/-- Compatible ring identifications with a separable field extension give ind-smoothness.

Source: Stacks Project, Algebra, Lemma 07BV, and Smoothing Ring Maps,
Lemma 07FE (lemma-resolve-special), final residue-field argument.
(blueprint: lem-weil-pbc-separable-ind-smooth-transport).

Proof: The finitely generated smooth k-subalgebras of K form a nonempty directed
cover by Lemma 07BV. Pull each scalar action back along R ≃ k and lift its carrier
to the joint universe. Inclusions remain R-algebra maps. Smoothness is preserved
because R → k is an isomorphism and smooth maps compose. Their cocone to ULift K
is a colimit: every element is in a subalgebra, and equality of two elements from
one subalgebra is detected by its injective inclusion. The forgetful functor to
types reflects this filtered colimit. Lift the indexing category to the same universe.
Finally the compatible target ring equivalence is an R-algebra equivalence to
ULift K, so transport the colimit presentation along its inverse. No finite-degree
or algebraicity assumption on K/k is used. -/
theorem ind_smooth_of_separable_ringEquivs
    {k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]
    {R : Type u} {S : Type (max u v w)}
    [CommRing R] [CommRing S] [Algebra R S]
    (hsep : IsSeparableExtension k K) (eR : R ≃+* k) (eS : S ≃+* K)
    (hcompat : ∀ r : R, eS (algebraMap R S r) = algebraMap k K (eR r)) :
    ObjectProperty.ind.{max u v w}
      (fun B : CommAlgCat.{max u v w} R ↦ Smooth R B) (CommAlgCat.of R S) := by
  classical
  let A := {A : Subalgebra k K // Smooth k A ∧ A.FG}
  obtain ⟨hne, hdir, hcover, _⟩ :=
    FieldTheory.separable_extension_is_filtered_colimit_smooth hsep
  let : Nonempty A := hne
  let : IsDirectedOrder A := ⟨hdir⟩
  let J := ULift.{max u v w} A
  let : IsDirectedOrder J := ⟨by
    intro a b
    obtain ⟨c, ha, hb⟩ := hdir a.down b.down
    exact ⟨⟨c⟩, ha, hb⟩⟩
  let : Algebra R k := eR.toRingHom.toAlgebra
  let : Algebra R K := ((algebraMap k K).comp eR.toRingHom).toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq' rfl
  let aR (a : A) : Algebra R a.1 :=
    ((algebraMap k a.1).comp eR.toRingHom).toAlgebra
  let D : J ⥤ CommAlgCat.{max u v w} R :=
    { obj := fun a ↦ by
        let := aR a.down
        exact CommAlgCat.of R (ULift.{max u v} a.down.1)
      map := fun {a b} f ↦ by
        let := aR a.down
        let := aR b.down
        exact CommAlgCat.ofHom
          { __ := (ULift.ringEquiv.symm.toRingHom.comp
              ((Subalgebra.inclusion
                (show a.down.1 ≤ b.down.1 from @leOfHom J _ a b f)).toRingHom.comp
                ULift.ringEquiv.toRingHom))
            commutes' := fun r ↦ by
              apply ULift.down_injective
              exact (Subalgebra.inclusion
                (show a.down.1 ≤ b.down.1 from @leOfHom J _ a b f)).commutes (eR r) }
      map_id := by intros; ext; rfl
      map_comp := by intros; ext; rfl }
  let c : Cocone D :=
    { pt := CommAlgCat.of R (ULift.{max u v} K)
      ι :=
        { app := fun a ↦ by
            let := aR a.down
            exact CommAlgCat.ofHom
              { __ := ULift.ringEquiv.symm.toRingHom.comp
                  (a.down.1.val.toRingHom.comp ULift.ringEquiv.toRingHom)
                commutes' := fun r ↦ by
                  apply ULift.down_injective
                  exact a.down.1.val.commutes (eR r) }
          naturality := by intros; ext; rfl } }
  have hc : IsColimit c := by
    apply algebraIsColimitOfForget
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨a, ha⟩ := hcover x.down
      exact ⟨⟨a⟩, ⟨⟨x.down, ha⟩⟩, rfl⟩
    · intro a x y hxy
      refine ⟨a, 𝟙 a, ?_⟩
      apply ULift.down_injective
      apply Subtype.ext
      exact congrArg ULift.down hxy
  have hD : ∀ j, Smooth R (D.obj j) := by
    intro j
    let := aR j.down
    have : Smooth k j.down.1 := j.down.2.1
    have : Smooth k (ULift.{max u v} j.down.1) := Smooth.of_equiv ULift.algEquiv.symm
    apply RingHom.smooth_algebraMap.mp
    change ((algebraMap k (ULift.{max u v} j.down.1)).comp eR.toRingHom).Smooth
    exact (RingHom.Smooth.of_bijective (f := eR.toRingHom) eR.bijective).comp
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have hK : ObjectProperty.ind.{max u v w}
      (fun B : CommAlgCat.{max u v w} R ↦ Smooth R B)
      (CommAlgCat.of R (ULift.{max u v} K)) :=
    ⟨J, inferInstance, inferInstance, ⟨D, c.ι, hc⟩, hD⟩
  let e : S ≃ₐ[R] ULift.{max u v} K :=
    { __ := eS.trans ULift.ringEquiv.symm
      commutes' := fun r ↦ by
        apply ULift.down_injective
        exact hcompat r }
  exact (ObjectProperty.ind _).prop_of_iso (CommAlgCat.isoMk e).symm hK

end Algebra
