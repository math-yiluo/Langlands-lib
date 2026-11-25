/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionTransport
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionBijective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionAugmentation

/-! # Subset coordinates for the alternating tuple total

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-coordinates).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

/-- The tuple total has the displayed subset coordinates, including its differential
and the restriction of a section into the singleton coordinates. The source complex
and a map from it are not part of this statement.

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-coordinates).

Proof: Send an increasing tuple to its range; its inverse is the increasing enumeration
of a finite subset. Its intersection is the preimage of the basic open of the product.
Apply the explicit restriction section identification on each intersection. In degree n
only the columns 0 through r-1 occur. Regroup their finite direct sum by cardinality,
identifying the coefficient degree with n+1-card S, and compose with tau. This gives
b and its inverse. For the differential, deleting position k erases the corresponding
index j, and k counts the indices less than j; the horizontal signs and restrictions
therefore agree. The vertical sign is (-1)^(card S-1). Naturality of section transport
identifies coefficient differentials and proof irrelevance identifies equality
transports. Use the assumed differential formula to obtain the first equation.
The degree-zero column consists precisely of the singleton coordinates: restricting
a section gives the displayed function, and all other columns receive zero. Expanding
the explicit augmentation gives the second equation. If r=0 both finite coordinate
families are empty and the total is zero. Repeated opens keep their distinct indices;
empty intersections have zero sections by the sheaf axiom. -/
theorem principalOpenCech_subset_coordinates
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    let V : (Spec (.of A)).Opens := ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun S ↦ PrimeSpectrum.basicOpen (∏ j ∈ S, f j)
    ∀ (T : CochainComplex (ModuleCat.{u} A) ℤ)
      (τ : ∀ n : ℤ, T.X n ≅ ModuleCat.of A
        (∀ S : {S : Finset (Fin r) // S.Nonempty},
          (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.obj (op (D S.val))))
      (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (hls : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → D S.val ≤ V)
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (hes : ∀ S : {S : Finset (Fin r) // S.Nonempty}, S.val.card = 1 → ∀ n : ℤ,
        n = n + 1 - (S.val.card : ℤ)),
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
      let R := SheafOfModules.overFunctor.{u}
        (moduleRings (Spec (.of A)).toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)
      let J' := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj J
      let U : Fin r → V.toScheme.Opens :=
        fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
      let F := (forget₂ (ModuleCat.{u} A) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let G := (forget₂
        (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
        AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)
      let B := G.obj ((alternatingCechTotalFunctor U).obj J')
      ∃ b : ∀ n : ℤ, (F.obj T).X n ≅ B.X n,
        (∀ n : ℤ, (b n).hom ≫ B.d n (n + 1) =
          (F.obj T).d n (n + 1) ≫ (b (n + 1)).hom) ∧
        (∀ (n : ℤ) (s : (modulesSpecToSheaf.obj (J.X n)).obj.obj (op V)),
          (b n).hom ((τ n).inv (fun S ↦ if h : S.val.card = 1 then
            (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
              (homOfLE (hls S h)).op
              ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
                (op V) s) else 0)) =
            (G.map ((alternatingCechAugmentation U).app J')).f n
              (by
                change (forget₂
                  (ModuleCat.{u} ((moduleRings V.toScheme.toRingedSpace).obj.obj (op ⊤)))
                  AddCommGrpCat).obj
                    ((RingedSpace.globalSectionsFunctor V.toScheme.toRingedSpace).obj
                      (R.obj (J.X n)))
                exact (principalOpenSectionTransport A V (J.X n)).hom s)) := by
  intro V D T τ hle hls he hes hdT
  let F := forget₂ (ModuleCat.{u} A) AddCommGrpCat
  let b (n : ℤ) := F.mapIso (τ n) ≪≫ principalSubsetInsertionIso A r f J n
  refine ⟨b, ?_, ?_⟩
  · intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (principalSubsetTotal A r f J).d n (n + 1)
      (principalSubsetInsertion A r f J n ((τ n).hom s)) =
        principalSubsetInsertion A r f J (n + 1) ((τ (n + 1)).hom (T.d n (n + 1) s))
    rw [principalSubsetInsertion_differential A r f J hle he]
    congr 1
    funext S
    exact (hdT n s S).symm
  · intro n s
    change principalSubsetInsertion A r f J n
      ((τ n).hom ((τ n).inv (fun S ↦ if h : S.val.card = 1 then
        (modulesSpecToSheaf.obj (J.X (n + 1 - (S.val.card : ℤ)))).obj.map
          (homOfLE (hls S h)).op
          ((modulesSpecToSheaf.map (eqToHom (congrArg J.X (hes S h n)))).hom.app
            (op V) s) else 0))) = _
    rw [Iso.inv_hom_id_apply]
    exact principalSubsetInsertion_augmentation A r f J hls hes n s

end AlgebraicGeometry
