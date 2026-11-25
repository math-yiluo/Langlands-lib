/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetCoordinates

/-! # Subset coordinates and the alternating Čech augmentation on the union

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

-- The mapped-complex section transports require extra definitional equality checks.
/-- The displayed subset-coordinate augmentation is the increasing-tuple augmentation
on the open union, after forgetting scalar actions. This is a chain-level coordinate
comparison for arbitrary coefficient complexes, with no K-injectivity assumption.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM, the increasing
index convention for alternating Čech cochains.
(blueprint: lem-sc-principal-open-cech-subset-comparison).

Proof: Set V to the union of the principal opens and restrict J to V by overFunctor
followed by overEquiv. A restricted module's sections on an open of V are its original
sections on the corresponding open of Spec A. Forgetting the scalar actions therefore
identifies its global sections with J(V), naturally in coefficient morphisms. Compose
these identifications with sigma to identify K with the section complex on V.
In total degree n, the alternating total is a coproduct over p+q=n of products indexed
by increasing (p+1)-tuples. Only 0 <= p < r occur. Send an increasing tuple to its range
S; its order embedding is the unique increasing enumeration of S. This identifies
p with card S - 1 and q with n + 1 - card S. The corresponding intersection is the
preimage in V of D(product of the f_j over S), since basic opens take products to
intersections. Use section transport along this equality and coefficient transport
along q = n + 1 - card S. Grouping the finite family of subset coordinates by
cardinality is the inverse map, so these maps are degreewise additive isomorphisms.
Deleting position k in the enumeration erases its element j, and k is exactly the
number of elements of S smaller than j. Thus the horizontal signs and restriction
maps agree. The vertical sign is (-1)^p = (-1)^(card S - 1), and the coefficient
transports agree by proof irrelevance. The assumed differential equations make the
degreewise identifications chain isomorphisms. The source differential equation
makes the source identification a chain isomorphism as well. On singleton coordinates
the assumed augmentation equation is restriction from V, and in higher columns it
is zero; hence the two isomorphisms commute with the augmentations and give an arrow
isomorphism. For r=0 both coordinate products and the tuple total are zero, while V
is empty and the sheaf axiom makes its sections zero. Repeated principal opens cause
no ambiguity because the indexing is by indices, and empty intersections have zero
sections. No assertion about cohomology is used in this comparison. -/
theorem principalOpenCech_subset_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (K T : CochainComplex (ModuleCat.{u} A) ℤ)
      (σ : ∀ n : ℤ, K.X n ≅ (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V))
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (α : K ⟶ T)
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
      (∀ (n : ℤ) (s : K.X n),
        (σ (n + 1)).hom (K.d n (n + 1) s) =
          (modulesSpecToSheaf.map (J.d n (n + 1))).hom.app (op V) ((σ n).hom s)) →
      (∀ (n : ℤ) (s : T.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ (n + 1)).hom (T.d n (n + 1) s) S =
          (-1 : A) ^ (S.val.card - 1) •
            (modulesSpecToSheaf.map
              (J.d (n + 1 - (S.val.card : ℤ)) (n + 1 + 1 - (S.val.card : ℤ)))).hom.app
                (op (D S.val)) ((τ n).hom s S) +
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val))) ((τ n).hom s ⟨S.val.erase j.val, h⟩))
          else 0) →
      (∀ (n : ℤ) (s : K.X n) (S : {S : Finset (Fin r) // S.Nonempty}),
        (τ n).hom (α.f n s) S = if h : S.val.card = 1 then
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
            (homOfLE (hls S h)).op
            ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
              (op V) ((σ n).hom s)) else 0) →
      let R := SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)
      let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
      let U : Fin r → V.toScheme.Opens :=
        fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
      Nonempty (Arrow.mk
        (((forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) ≅
        Arrow.mk
          (((forget₂
            (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
            AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((alternatingCechAugmentation U).app J'))) := by
  intro V D K T σ τ α hle hls he hes hdK hdT hα
  let R := SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
    (Scheme.Modules.overEquiv V).functor
  let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
  let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
  let F := (forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let G := (forget₂
    (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)
  let β := G.map ((alternatingCechAugmentation U).app J')
  let C := G.obj
    (((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J')
  let a (n : ℤ) : (F.obj K).X n ≅ C.X n := by
    change (forget₂ (ModuleCat.{u} A) AddCommGrpCat).obj (K.X n) ≅
      (forget₂
        (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat).obj
          ((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).obj (R.obj (J.X n)))
    exact (forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapIso (σ n) ≪≫
      principalOpenSectionTransport A V (J.X n)
  obtain ⟨b, hb, haug⟩ :=
    principalOpenCech_subset_coordinates A r f J T τ hle hls he hes hdT
  have ha (n : ℤ) : (a n).hom ≫ C.d n (n + 1) =
      (F.obj K).d n (n + 1) ≫ (a (n + 1)).hom := by
    apply ConcreteCategory.hom_ext
    intro s
    change (R.map (J.d n (n + 1))).app ⊤
      ((principalOpenSectionTransport A V (J.X n)).hom ((σ n).hom s)) =
      (principalOpenSectionTransport A V (J.X (n + 1))).hom
        ((σ (n + 1)).hom (K.d n (n + 1) s))
    rw [hdK]
    exact (principalOpenSectionTransport_natural A V (J.d n (n + 1))
      ((σ n).hom s)).symm
  let e₁ := HomologicalComplex.Hom.isoOfComponents a (by
    intro n m hnm
    have hm : m = n + 1 := by simpa using hnm.symm
    subst m
    exact ha n)
  let e₂ := HomologicalComplex.Hom.isoOfComponents b (by
    intro n m hnm
    have hm : m = n + 1 := by simpa using hnm.symm
    subst m
    exact hb n)
  change Nonempty (Arrow.mk (F.map α) ≅ Arrow.mk β)
  refine ⟨Arrow.isoMk' (F.map α) β e₁ e₂ ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change β.f n ((a n).hom s) = (b n).hom (α.f n s)
  have hc : α.f n s = (τ n).inv (fun S ↦ if h : S.val.card = 1 then
      (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
        (homOfLE (hls S h)).op
        ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
          (op V) ((σ n).hom s)) else 0) := by
    apply (ConcreteCategory.bijective_of_isIso (τ n).hom).injective
    change (τ n).hom (α.f n s) = _
    simp only [Iso.inv_hom_id_apply]
    funext S
    exact hα n s S
  rw [hc]
  exact (haug n ((σ n).hom s)).symm

end AlgebraicGeometry
