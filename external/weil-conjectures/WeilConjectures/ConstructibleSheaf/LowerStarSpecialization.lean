/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianLift
public import WeilConjectures.ConstructibleSheaf.LowerStarOpenStalk

/-!
# Specialization of the stalks of a direct image to a strictly henselian point

Let `A` be a strictly henselian local ring with residue field `κ`, `a : Spec A ⟶ X` a morphism,
`ι : A → Ω` a ring map to a separably closed field and `j : U ⟶ X` a morphism through which the
geometric point `η : Spec Ω ⟶ Spec A ⟶ X` factors. Write `s̄ : Spec κ ⟶ Spec A ⟶ X` for the
closed geometric point.

An étale neighbourhood `(V, v)` of `s̄` lifts uniquely to `Spec A`
(`AlgebraicGeometry.Scheme.henselianLift`), so that `η` lifts to `V`, hence to `V ×_X U`; this
is the *specialization* from the fibre functor of `s̄` to that of `η` composed with base change
(`AlgebraicGeometry.Scheme.specializationFiber`). On stalks of a sheaf `F` on `U` it gives the
specialization map

  `(j_* F)_{s̄} ⟶ F_η`

(`AlgebraicGeometry.Etale.specializationStalk`), sending the germ at `(V, v)` of a section of `F`
over `V ×_X U` to its germ at the lifted point.

- It is equivariant for automorphisms of `A` over `X` and compatible automorphisms of `Ω`
  (`AlgebraicGeometry.Etale.specializationStalk_comp_stalkHom`), since the lift is unique. In
  particular its image consists of invariants of the automorphisms of `Ω` coming from
  automorphisms of `A` inducing the identity on `κ`, i.e. of the inertia group.
- For `X` locally noetherian with étale local rings that are domains (e.g. regular), `j` an open
  immersion and `F` locally constant, it is injective
  (`AlgebraicGeometry.Etale.injective_specializationStalk`): two sections of `F` over the
  punctured part of an irreducible neighbourhood with the same germ at a geometric point agree.

The automorphisms of a geometric point `s : Spec Ω ⟶ S` coming from ring automorphisms `σ` of `Ω`
with `Spec σ ≫ s = s` act on the stalks of sheaves at `s` (`AlgebraicGeometry.Etale.stalkHom`),
on germs by `(V, t) ↦ (V, Spec σ ≫ t)`; for a geometric point over a field `K` this is the action
of `Gal(Ω / K)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Scheme

section Aut

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The endomorphism of the geometric point `s : Spec Ω ⟶ S` of the small étale site induced by
a ring endomorphism `σ` of `Ω` with `Spec σ ≫ s = s`: on fibre functors it sends a lift
`t : Spec Ω ⟶ V` of `s` to `Spec σ ≫ t`. -/
noncomputable def pointSmallEtaleHom (σ : Ω →+* Ω)
    (hσ : Spec.map (CommRingCat.ofHom σ) ≫ s = s) : pointSmallEtale s ⟶ pointSmallEtale s where
  hom :=
    { app V := TypeCat.ofHom fun (t : (pointSmallEtale s).fiber.obj V) ↦
        Over.homMk (Spec.map (CommRingCat.ofHom σ) ≫ t.left) (by
        have := Over.w t
        dsimp at this ⊢
        rw [Category.assoc, this, hσ])
      naturality V W f := by
        ext t
        exact Over.OverMorphism.ext (Category.assoc _ _ _).symm }

@[simp]
lemma pointSmallEtaleHom_hom_app_left (σ : Ω →+* Ω)
    (hσ : Spec.map (CommRingCat.ofHom σ) ≫ s = s) (V : S.Etale)
    (t : (pointSmallEtale s).fiber.obj V) :
    ((pointSmallEtaleHom s σ hσ).hom.app V t).left = Spec.map (CommRingCat.ofHom σ) ≫ t.left :=
  rfl

/-- On germs, the endomorphism of the stalks induced by
`AlgebraicGeometry.Scheme.pointSmallEtaleHom`
moves the geometric point. -/
@[reassoc]
lemma toPresheafFiber_pointSmallEtaleHom_sheafFiber_app {C : Type*} [Category* C]
    [HasColimitsOfSize.{u, u} C] (σ : Ω →+* Ω) (hσ : Spec.map (CommRingCat.ofHom σ) ≫ s = s)
    (G : Sheaf S.smallEtaleTopology C) (V : S.Etale) (t : (pointSmallEtale s).fiber.obj V) :
    (pointSmallEtale s).toPresheafFiber V t ((sheafToPresheaf _ _).obj G) ≫
        (pointSmallEtaleHom s σ hσ).sheafFiber.app G =
      (pointSmallEtale s).toPresheafFiber V ((pointSmallEtaleHom s σ hσ).hom.app V t)
        ((sheafToPresheaf _ _).obj G) := by
  simp only [GrothendieckTopology.Point.Hom.sheafFiber, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _


lemma pointSmallEtaleHom_hom_app_eq_self (σ : Ω →+* Ω) (hσ' : ∀ x, σ x = x)
    (hσ : Spec.map (CommRingCat.ofHom σ) ≫ s = s) (V : S.Etale)
    (t : (pointSmallEtale s).fiber.obj V) : (pointSmallEtaleHom s σ hσ).hom.app V t = t := by
  obtain rfl : σ = RingHom.id Ω := RingHom.ext hσ'
  exact Over.OverMorphism.ext (by
    rw [pointSmallEtaleHom_hom_app_left]
    exact (congrArg (· ≫ t.left) (Spec.map_id (CommRingCat.of Ω))).trans (Category.id_comp _))

/-- An endomorphism of `Ω` acting trivially induces the identity on stalks. -/
lemma pointSmallEtaleHom_sheafFiber_app_eq_id {C : Type*} [Category* C]
    [HasColimitsOfSize.{u, u} C] (σ : Ω →+* Ω) (hσ' : ∀ x, σ x = x)
    (hσ : Spec.map (CommRingCat.ofHom σ) ≫ s = s) (G : Sheaf S.smallEtaleTopology C) :
    (pointSmallEtaleHom s σ hσ).sheafFiber.app G = 𝟙 _ := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ fun V t ↦ ?_
  rw [toPresheafFiber_pointSmallEtaleHom_sheafFiber_app,
    pointSmallEtaleHom_hom_app_eq_self s σ hσ' hσ V t]
  exact (Category.comp_id _).symm
end Aut

section Specialization

variable {X U : Scheme.{u}} (j : U ⟶ X) {A : Type u} [CommRing A]
  [IsStrictlyHenselianLocalRing A] (a : Spec (.of A) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ι : CommRingCat.of A ⟶ CommRingCat.of Ω) (η : Spec (.of Ω) ⟶ U)
  (hη : η ≫ j = Spec.map ι ≫ a)

lemma comp_hom_eq_of_mem_fiber {V : X.Etale}
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    v.left ≫ V.hom = closedGeometricPoint A ≫ a :=
  Over.w v

/-- **Specialization on fibre functors.** A lift `v : Spec κ ⟶ V` of the closed geometric point
`Spec κ ⟶ Spec A ⟶ X` to an étale `X`-scheme `V` lifts uniquely to `Spec A ⟶ V`
(`AlgebraicGeometry.Scheme.henselianLift`); composing with `Spec Ω ⟶ Spec A` and pairing with
`η` gives a lift of `η` to `V ×_X U`. -/
noncomputable def specializationFiber (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (pointSmallEtale η).fiber.obj ((MorphismProperty.Over.pullback @Etale ⊤ j).obj V) :=
  Over.homMk (pullback.lift (Spec.map ι ≫ henselianLift a V.hom v.left
      (comp_hom_eq_of_mem_fiber a v)) η (by
    rw [Category.assoc, henselianLift_comp, hη])) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma specializationFiber_left_fst (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (specializationFiber j a ι η hη V v).left ≫ pullback.fst V.hom j =
      Spec.map ι ≫ henselianLift a V.hom v.left (comp_hom_eq_of_mem_fiber a v) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma specializationFiber_left_snd (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (specializationFiber j a ι η hη V v).left ≫ pullback.snd V.hom j = η :=
  pullback.lift_snd _ _ _

lemma specializationFiber_naturality {V V' : X.Etale} (f : V ⟶ V')
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (pointSmallEtale η).fiber.map ((MorphismProperty.Over.pullback @Etale ⊤ j).map f)
        (specializationFiber j a ι η hη V v) =
      specializationFiber j a ι η hη V' ((pointSmallEtale _).fiber.map f v) := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · change ((specializationFiber j a ι η hη V v).left ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ j).map f).left) ≫ _ = _
    rw [MorphismProperty.Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      specializationFiber_left_fst_assoc, specializationFiber_left_fst,
      henselianLift_comp_hom a V.hom V'.hom f.left (MorphismProperty.Over.w f)]
    rfl
  · change ((specializationFiber j a ι η hη V v).left ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ j).map f).left) ≫ _ = _
    rw [MorphismProperty.Over.pullback_map_left, Category.assoc, pullback.lift_snd,
      specializationFiber_left_snd, specializationFiber_left_snd]

lemma henselianLift_specMap_comp (τ : A →+* A) (hτa : Spec.map (CommRingCat.ofHom τ) ≫ a = a)
    (τ' : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A)
    (hτ : closedGeometricPoint A ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A) {V : Scheme.{u}} (p : V ⟶ X)
    [AlgebraicGeometry.Etale p] (v : Spec (.of (IsLocalRing.ResidueField A)) ⟶ V)
    (hv : v ≫ p = closedGeometricPoint A ≫ a) :
    henselianLift a p (Spec.map (CommRingCat.ofHom τ') ≫ v)
        (by rw [Category.assoc, hv, ← Category.assoc, ← hτ, Category.assoc, hτa]) =
      Spec.map (CommRingCat.ofHom τ) ≫ henselianLift a p v hv :=
  henselianLift_eq _ _ _ _ _ (by rw [Category.assoc, henselianLift_comp, hτa])
    (by rw [← Category.assoc, hτ, Category.assoc, closedGeometricPoint_henselianLift])

lemma comp_closedGeometricPoint_comp_eq (τ : A →+* A)
    (hτa : Spec.map (CommRingCat.ofHom τ) ≫ a = a)
    (τ' : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A)
    (hτ : closedGeometricPoint A ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A) :
    Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A ≫ a = closedGeometricPoint A ≫ a := by
  rw [← Category.assoc, ← hτ, Category.assoc, hτa]

/-- **Equivariance of the specialization on fibre functors.** For an endomorphism `τ` of `A`
over `X` inducing `τ'` on the residue field, and an endomorphism `σ` of `Ω` with `σ ∘ ι = ι ∘ τ`
fixing `η`, the specialization intertwines `Spec τ'` and `Spec σ`. -/
lemma specializationFiber_pointSmallEtaleHom (τ : A →+* A)
    (hτa : Spec.map (CommRingCat.ofHom τ) ≫ a = a)
    (τ' : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A)
    (hτ : closedGeometricPoint A ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A) (σ : Ω →+* Ω)
    (hσι : ι ≫ CommRingCat.ofHom σ = CommRingCat.ofHom τ ≫ ι)
    (hση : Spec.map (CommRingCat.ofHom σ) ≫ η = η) (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    specializationFiber j a ι η hη V ((pointSmallEtaleHom _ τ'
        (comp_closedGeometricPoint_comp_eq a τ hτa τ' hτ)).hom.app V v) =
      (pointSmallEtaleHom η σ hση).hom.app _ (specializationFiber j a ι η hη V v) := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · change (specializationFiber j a ι η hη V _).left ≫ _ =
      (Spec.map (CommRingCat.ofHom σ) ≫ (specializationFiber j a ι η hη V v).left) ≫ _
    rw [Category.assoc, specializationFiber_left_fst, specializationFiber_left_fst]
    have h := henselianLift_specMap_comp a τ hτa τ' hτ V.hom v.left
      (comp_hom_eq_of_mem_fiber a v)
    simp only [pointSmallEtaleHom_hom_app_left] at h ⊢
    rw [h, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hσι]
  · change (specializationFiber j a ι η hη V _).left ≫ _ =
      (Spec.map (CommRingCat.ofHom σ) ≫ (specializationFiber j a ι η hη V v).left) ≫ _
    rw [Category.assoc, specializationFiber_left_snd, specializationFiber_left_snd, hση]

end Specialization

end Scheme

namespace Etale

section Specialization

variable {X U : Scheme.{u}} (j : U ⟶ X) {A : Type u} [CommRing A]
  [IsStrictlyHenselianLocalRing A] (a : Spec (.of A) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ι : CommRingCat.of A ⟶ CommRingCat.of Ω) (η : Spec (.of Ω) ⟶ U)
  (hη : η ≫ j = Spec.map ι ≫ a) {Λ : Type (u + 1)} [Ring Λ]

/-- **The specialization map of the stalks of a direct image.** For `A` strictly henselian with
closed geometric point `s̄ : Spec κ ⟶ Spec A ⟶ X` and a geometric point `η : Spec Ω ⟶ U` over
`Spec Ω ⟶ Spec A ⟶ X`, the map `(j_* F)_{s̄} ⟶ F_η` sending the germ at `(V, v)` of a section
of `F` over `V ×_X U` to its germ at the specialization of `v`
(`AlgebraicGeometry.Scheme.specializationFiber`). -/
noncomputable def specializationStalk (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtale (closedGeometricPoint A ≫ a)).sheafFiber.obj
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ⟶ (pointSmallEtale η).sheafFiber.obj F :=
  (pointSmallEtale _).presheafFiberDesc
    (fun V v ↦ (pointSmallEtale η).toPresheafFiber _ (specializationFiber j a ι η hη V v) F.obj)
    (fun V V' f v ↦ by
      change F.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ j).map f).op ≫ _ = _
      rw [GrothendieckTopology.Point.toPresheafFiber_w, specializationFiber_naturality])

@[reassoc (attr := simp)]
lemma toPresheafFiber_specializationStalk
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V) :
    (pointSmallEtale _).toPresheafFiber V v
        ((sheafToPresheaf _ _).obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) ≫
        specializationStalk j a ι η hη F =
      (pointSmallEtale η).toPresheafFiber _ (specializationFiber j a ι η hη V v)
        ((sheafToPresheaf _ _).obj F) :=
  GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

lemma specializationStalk_toPresheafFiber
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (v : (pointSmallEtale (closedGeometricPoint A ≫ a)).fiber.obj V)
    (z : ToType (((j)_*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op V))) :
    specializationStalk j a ι η hη F ((pointSmallEtale _).toPresheafFiber V v
        ((sheafToPresheaf _ _).obj ((j)_*[ModuleCat.{u + 1} Λ].obj F)) z) =
      (pointSmallEtale η).toPresheafFiber _ (specializationFiber j a ι η hη V v)
        ((sheafToPresheaf _ _).obj F) z :=
  ConcreteCategory.congr_hom (toPresheafFiber_specializationStalk j a ι η hη F V v) z

/-- **Equivariance of the specialization map.** An endomorphism `τ` of `A` over `X` inducing `τ'`
on the residue field and a compatible endomorphism `σ` of `Ω` fixing `η` act on the two stalks,
and the specialization map intertwines these actions. -/
theorem stalkHom_comp_specializationStalk (τ : A →+* A)
    (hτa : Spec.map (CommRingCat.ofHom τ) ≫ a = a)
    (τ' : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A)
    (hτ : closedGeometricPoint A ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ closedGeometricPoint A) (σ : Ω →+* Ω)
    (hσι : ι ≫ CommRingCat.ofHom σ = CommRingCat.ofHom τ ≫ ι)
    (hση : Spec.map (CommRingCat.ofHom σ) ≫ η = η)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (pointSmallEtaleHom _ τ' (comp_closedGeometricPoint_comp_eq a τ hτa τ' hτ)).sheafFiber.app
        ((j)_*[ModuleCat.{u + 1} Λ].obj F) ≫ specializationStalk j a ι η hη F =
      specializationStalk j a ι η hη F ≫ (pointSmallEtaleHom η σ hση).sheafFiber.app F := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ fun V v ↦ ?_
  rw [toPresheafFiber_pointSmallEtaleHom_sheafFiber_app_assoc,
    toPresheafFiber_specializationStalk, toPresheafFiber_specializationStalk_assoc,
    toPresheafFiber_pointSmallEtaleHom_sheafFiber_app,
    specializationFiber_pointSmallEtaleHom j a ι η hη τ hτa τ' hτ σ hσι hση]

omit [IsStrictlyHenselianLocalRing A] in
/-- In a locally noetherian scheme whose étale `X`-schemes have local rings that are domains,
every étale neighbourhood of a geometric point is refined by one with irreducible underlying
space. -/
lemma exists_irreducibleSpace_refinement
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (s : Spec (.of Ω') ⟶ X)
    (V : X.Etale) (v : (pointSmallEtale s).fiber.obj V) :
    ∃ (W : X.Etale) (w : (pointSmallEtale s).fiber.obj W) (k : W ⟶ V),
      (pointSmallEtale s).fiber.map k w = v ∧ IrreducibleSpace W.left := by
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian (Y := X) V.hom
  obtain ⟨O, hO, hOirr⟩ := exists_isOpen_irreducibleSpace_of_isDomain_stalk (hX V)
    (v.left (IsLocalRing.closedPoint Ω'))
  obtain ⟨v', hv'⟩ := exists_pointSmallEtale_fiber_ofOpens s v O (by
    rintro _ ⟨z, rfl⟩
    have : Subsingleton (Spec (.of Ω')) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω'))
    rwa [@Subsingleton.elim (Spec (.of Ω')) this z (IsLocalRing.closedPoint Ω')])
  exact ⟨Etale.ofOpens V O, v', Etale.ofOpensι V O, hv', hOirr⟩

/-- **The specialization map is injective** for a locally constant sheaf `F` on an open `U` of a
locally noetherian scheme `X` whose étale `X`-schemes have local rings that are domains (for
instance `X` regular): two germs at the closed geometric point are represented over an
irreducible étale neighbourhood `W`, whose punctured part `W ×_X U` is connected, and sections of
a locally constant sheaf over a connected étale scheme are determined by their germ at one
geometric point. -/
theorem injective_specializationStalk [IsOpenImmersion j]
    (hX : ∀ (W : X.Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    [IsLocallyNoetherian X] (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf F] : Function.Injective (specializationStalk j a ι η hη F) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro p₁ p₂ h
  obtain ⟨V, v, z₁, z₂, rfl, rfl⟩ :=
    (pointSmallEtale (closedGeometricPoint A ≫ a)).toPresheafFiber_jointly_surjective₂ p₁ p₂
  obtain ⟨W, w, k, rfl, hW⟩ := exists_irreducibleSpace_refinement hX _ V v
  rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply,
    ← GrothendieckTopology.Point.toPresheafFiber_w_apply] at h ⊢
  rw [specializationStalk_toPresheafFiber, specializationStalk_toPresheafFiber] at h
  have : PreconnectedSpace ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W).left :=
    @preconnectedSpace_pullback_of_irreducibleSpace _ _ _ hW W.hom j _
  rw [injective_toPresheafFiber_of_preconnectedSpace F η _ h]

end Specialization

end Etale

end AlgebraicGeometry
