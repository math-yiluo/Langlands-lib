/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.OpenClosed

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem constructible_essentiallySmall
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    EssentiallySmall.{u + 1}
      (ObjectProperty.FullSubcategory
        (IsConstructibleEtaleModuleSheaf (T := X) (Λ := Λ))) := by
  classical
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let P : X.Etale → C := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  let I : Type (u + 1) := Σ n m : ℕ, Σ U : Fin n → X.Etale,
    Σ V : Fin m → X.Etale, (∐ fun j ↦ P (V j)) ⟶ (∐ fun i ↦ P (U i))
  let Q : ObjectProperty C := .ofObj (fun i : I ↦ Limits.cokernel i.2.2.2.2)
  have h : IsConstructibleEtaleModuleSheaf (T := X) (Λ := Λ) ≤ Q.isoClosure := by
    intro G hG
    obtain ⟨n, m, U, V, _, _, f, g, w, ⟨hg⟩⟩ :=
      exists_affine_free_etale_presentation X Λ G hG
    refine ⟨Limits.cokernel f,
      ObjectProperty.ofObj_apply (fun i : I ↦ Limits.cokernel i.2.2.2.2)
      (show I from ⟨n, m, U, V, f⟩), ?_⟩
    exact ⟨hg.coconePointUniqueUpToIso (Limits.colimit.isColimit _)⟩
  have : ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstructibleEtaleModuleSheaf (T := X) (Λ := Λ)) :=
    ⟨Q, inferInstance, h⟩
  infer_instance

/-- A small filtered system of constructible maps to `F`, with factorization and
refinement of relations tested on constructible sources.

Source: Stacks Project, Tags 03SA(3), 095N and 03RZ; the category of finite
presentations over `F` in Modules on Sites, Lemma 093C.
(blueprint: lem-weil-pbc-module-sheaf-colimit-constructible-data).

Proof: Choose representatives of constructible module sheaves. They form a set in
universe `u + 1`: by 095N each is the cokernel of a map between finite sums of the
extensions by zero of finite free modules on qcqs etale objects; these objects have
a small skeleton, and the morphisms form sets in this universe. Include the zero
sheaf, finite sums, and cokernels. These operations preserve constructibility by
03S8 and 03RZ. Take the category of pairs `(G, G -> F)` on these representatives,
with commuting triangles as morphisms, and its forgetful diagram `D`. It is small.
Zero gives an object, direct sum gives a common successor, and the cokernel of the
difference of parallel maps gives an equalizing successor, so it is filtered.
The maps to `F` give the natural transformation `ι`. Every constructible map to `F`
is an object up to an isomorphism, which proves factorization. Given the two
factorizations in the last condition, form the cokernel of the map from `G` to
`D.obj a ⊕ D.obj b` with components `p` and `-q`. The assumed equality makes the
map from the sum to `F` descend to this cokernel. Its two inclusions give `f, g`,
and the cokernel equation is precisely `p ≫ D.map f = q ≫ D.map g`.
This constructs the system and its relations without asserting a universal
property for arbitrary cocones. -/
theorem exists_filtered_constructible_data
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (A : Type (u + 1)) (_ : SmallCategory A) (_ : IsFiltered A)
      (D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (ι : D ⟶ (Functor.const A).obj F),
      (∀ a : A, IsConstructibleEtaleModuleSheaf (D.obj a)) ∧
      (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsConstructibleEtaleModuleSheaf G → ∀ p : G ⟶ F,
          ∃ (a : A) (q : G ⟶ D.obj a), q ≫ ι.app a = p) ∧
      (∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsConstructibleEtaleModuleSheaf G → ∀ (a b : A)
          (p : G ⟶ D.obj a) (q : G ⟶ D.obj b),
          p ≫ ι.app a = q ≫ ι.app b →
          ∃ (c : A) (f : a ⟶ c) (g : b ⟶ c), p ≫ D.map f = q ≫ D.map g) := by
  classical
  let C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let : Zero C := Limits.HasZeroObject.zero' C
  let P : ObjectProperty C := IsConstructibleEtaleModuleSheaf
  let B := CostructuredArrow P.ι F
  have : EssentiallySmall.{u + 1} P.FullSubcategory := constructible_essentiallySmall X Λ
  have hzero : P (0 : C) :=
    (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.of_isZero (Limits.isZero_zero _))
  have hsum (a b : P.FullSubcategory) : P (a.obj ⊞ b.obj) := by
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp a.property
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp b.property
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.biprod a.obj b.obj)
  have hcoker (a b : P.FullSubcategory) (f : a.obj ⟶ b.obj) : P (Limits.cokernel f) := by
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp a.property
    have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp b.property
    exact (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (IsConstructibleSheaf.cokernel f)
  have : IsFiltered B :=
    { nonempty := ⟨CostructuredArrow.mk (Y := (⟨0, hzero⟩ : P.FullSubcategory)) (0 : (0 : C) ⟶ F)⟩
      cocone_objs := by
        intro a b
        let c : B := CostructuredArrow.mk
          (Y := (⟨a.left.obj ⊞ b.left.obj, hsum _ _⟩ : P.FullSubcategory))
          (Limits.biprod.desc a.hom b.hom)
        refine ⟨c, CostructuredArrow.homMk ⟨Limits.biprod.inl⟩ ?_,
          CostructuredArrow.homMk ⟨Limits.biprod.inr⟩ ?_, trivial⟩ <;> simp [c, P]
      cocone_maps := by
        intro a b f g
        let d := f.left.hom - g.left.hom
        have hd : d ≫ b.hom = 0 := by
          dsimp [d]
          rw [Preadditive.sub_comp]
          exact sub_eq_zero.mpr ((CostructuredArrow.w f).trans (CostructuredArrow.w g).symm)
        let c : B := CostructuredArrow.mk
          (Y := (⟨Limits.cokernel d, hcoker _ _ d⟩ : P.FullSubcategory))
          (Limits.cokernel.desc d b.hom hd)
        let h : b ⟶ c := CostructuredArrow.homMk ⟨Limits.cokernel.π d⟩ (by simp [c])
        refine ⟨c, h, CostructuredArrow.hom_ext _ _ ?_⟩
        apply ObjectProperty.hom_ext
        change f.left.hom ≫ Limits.cokernel.π d = g.left.hom ≫ Limits.cokernel.π d
        have he := Limits.cokernel.condition d
        simpa only [d, Preadditive.sub_comp, sub_eq_zero] using he }
  let e := equivSmallModel.{u + 1} B
  let A := SmallModel.{u + 1} B
  have : IsFiltered A := IsFiltered.of_equivalence e
  let D : A ⥤ C := e.inverse ⋙ CostructuredArrow.proj P.ι F ⋙ P.ι
  let ι : D ⟶ (Functor.const A).obj F :=
    { app := fun a ↦ (e.inverse.obj a).hom
      naturality := fun a b f ↦ by simpa [D] using CostructuredArrow.w (e.inverse.map f) }
  refine ⟨A, inferInstance, inferInstance, D, ι, ?_, ?_, ?_⟩
  · intro a
    exact (e.inverse.obj a).left.property
  · intro G hG p
    let b : B := CostructuredArrow.mk (Y := (⟨G, hG⟩ : P.FullSubcategory)) p
    refine ⟨e.functor.obj b, (e.unitIso.app b).hom.left.hom, ?_⟩
    simpa [ι, b] using CostructuredArrow.w (e.unitIso.app b).hom
  · intro G hG a b p q hpq
    let r : B := CostructuredArrow.mk (Y := (⟨G, hG⟩ : P.FullSubcategory))
      (p ≫ ι.app a)
    let pa : r ⟶ e.inverse.obj a := CostructuredArrow.homMk ⟨p⟩ (by rfl)
    let qb : r ⟶ e.inverse.obj b := CostructuredArrow.homMk ⟨q⟩ hpq.symm
    let fa := IsFiltered.leftToMax (e.inverse.obj a) (e.inverse.obj b)
    let fb := IsFiltered.rightToMax (e.inverse.obj a) (e.inverse.obj b)
    let c := IsFiltered.coeq (pa ≫ fa) (qb ≫ fb)
    let k := IsFiltered.coeqHom (pa ≫ fa) (qb ≫ fb)
    let f : a ⟶ e.functor.obj c :=
      e.inverse.preimage (fa ≫ k ≫ (e.unitIso.app c).hom)
    let g : b ⟶ e.functor.obj c :=
      e.inverse.preimage (fb ≫ k ≫ (e.unitIso.app c).hom)
    refine ⟨e.functor.obj c, f, g, ?_⟩
    have he := IsFiltered.coeq_condition (pa ≫ fa) (qb ≫ fb)
    have he' := congrArg (fun h ↦ h.left.hom) he
    change p ≫ (D.map f) = q ≫ (D.map g)
    dsimp [D]
    rw [show e.inverse.map f = fa ≫ k ≫ (e.unitIso.app c).hom from
      e.inverse.map_preimage _, show e.inverse.map g = fb ≫ k ≫ (e.unitIso.app c).hom
      from e.inverse.map_preimage _]
    change (p ≫ fa.left.hom) ≫ k.left.hom = (q ≫ fb.left.hom) ≫ k.left.hom at he'
    change p ≫ (fa.left.hom ≫ k.left.hom ≫ (e.unitIso.app c).hom.left.hom) =
      q ≫ (fb.left.hom ≫ k.left.hom ≫ (e.unitIso.app c).hom.left.hom)
    simpa only [Category.assoc] using
      congrArg (fun h ↦ h ≫ (e.unitIso.app c).hom.left.hom) he'

end AlgebraicGeometry.Scheme
