import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Topology.Algebra.Group.Basic
import Langlands.Representation.Category.Basic

/-!
# Automorphisms of a site point and their action on fibers

The automorphism group of the actual Type-valued fiber functor has the topology
of pointwise convergence on fiber elements. Its action on module fibers is smooth.
-/

noncomputable section

namespace Langlands.Sheaf.PointAutomorphisms

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe w v u vA uA

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The automorphism group of the underlying functor of a site point. -/
def AutGroup (Φ : J.Point.{w}) := Aut Φ.fiber

instance (Φ : J.Point.{w}) : Group (AutGroup Φ) :=
  inferInstanceAs (Group (Aut Φ.fiber))

/-- The disjoint union of all fibers, equipped below with the discrete topology. -/
def FiberElements (Φ : J.Point.{w}) := Σ U : C, Φ.fiber.obj U

instance (Φ : J.Point.{w}) : TopologicalSpace (FiberElements Φ) := ⊥

instance (Φ : J.Point.{w}) : DiscreteTopology (FiberElements Φ) := ⟨rfl⟩

/-- A point automorphism permutes the elements in each fiber. -/
def toPerm (Φ : J.Point.{w}) : AutGroup Φ →* Equiv.Perm (FiberElements Φ) where
  toFun σ :=
    { toFun := fun p => ⟨p.1, σ.asIso.hom.app p.1 p.2⟩
      invFun := fun p => ⟨p.1, σ.asIso.inv.app p.1 p.2⟩
      left_inv := by
        rintro ⟨U, x⟩
        exact congrArg (Sigma.mk U) (ConcreteCategory.congr_hom (σ.asIso.hom_inv_id_app U) x)
      right_inv := by
        rintro ⟨U, x⟩
        exact congrArg (Sigma.mk U) (ConcreteCategory.congr_hom (σ.asIso.inv_hom_id_app U) x) }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Pointwise convergence on the discrete disjoint union of fibers. -/
instance (Φ : J.Point.{w}) : TopologicalSpace (AutGroup Φ) :=
  TopologicalSpace.induced (fun σ p => toPerm Φ σ p) inferInstance

theorem continuous_evaluation (Φ : J.Point.{w}) (p : FiberElements Φ) :
    Continuous (fun σ : AutGroup Φ => toPerm Φ σ p) :=
  (continuous_apply p).comp continuous_induced_dom

theorem toPerm_injective (Φ : J.Point.{w}) : Function.Injective (toPerm Φ) := by
  intro σ τ h
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext U
  ext x
  have h' := congrArg (fun f : Equiv.Perm (FiberElements Φ) => f ⟨U, x⟩) h
  change (⟨U, σ.asIso.hom.app U x⟩ : Σ V, Φ.fiber.obj V) = ⟨U, τ.asIso.hom.app U x⟩ at h'
  exact eq_of_heq (Sigma.mk.inj_iff.mp h').2

instance (Φ : J.Point.{w}) : T2Space (AutGroup Φ) :=
  T2Space.of_injective_continuous
    (fun _ _ h => toPerm_injective Φ (Equiv.ext (congrFun h)))
    continuous_induced_dom

theorem continuous_action (Φ : J.Point.{w}) :
    Continuous (fun p : AutGroup Φ × FiberElements Φ => toPerm Φ p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [continuousAt_prod_of_discrete_right]
  exact (continuous_evaluation Φ p.2).continuousAt

instance (Φ : J.Point.{w}) : IsTopologicalGroup (AutGroup Φ) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro p
    exact (continuous_action Φ).comp
      (continuous_fst.prodMk ((continuous_evaluation Φ p).comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro p
    apply continuous_iff_continuousAt.mpr
    intro σ
    have h : ∀ᶠ τ in 𝓝 σ, toPerm Φ τ (toPerm Φ σ⁻¹ p) = p :=
      ((isOpen_discrete ({p} : Set (FiberElements Φ))).preimage
        (continuous_evaluation Φ (toPerm Φ σ⁻¹ p))).mem_nhds (by simp)
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [h] with τ hτ
    apply (toPerm Φ τ).injective
    simpa using hτ.symm

/-- The stabilizer of a fiber element is an actual open subgroup. -/
def stabilizer (Φ : J.Point.{w}) (U : C) (x : Φ.fiber.obj U) :
    OpenSubgroup (AutGroup Φ) where
  carrier := {σ | σ.asIso.hom.app U x = x}
  one_mem' := rfl
  mul_mem' := by
    intro σ τ hσ hτ
    change σ.asIso.hom.app U (τ.asIso.hom.app U x) = x
    rw [hτ, hσ]
  inv_mem' := by
    intro σ hσ
    have h : σ.asIso.inv.app U (σ.asIso.hom.app U x) = x :=
      ConcreteCategory.congr_hom (σ.asIso.hom_inv_id_app U) x
    change σ.asIso.inv.app U x = x
    rwa [hσ] at h
  isOpen' := by
    have h := (isOpen_discrete ({⟨U, x⟩} : Set (FiberElements Φ))).preimage
      (continuous_evaluation Φ ⟨U, x⟩)
    convert h using 1
    ext σ
    change σ.asIso.hom.app U x = x ↔
      (⟨U, σ.asIso.hom.app U x⟩ : Σ V, Φ.fiber.obj V) = ⟨U, x⟩
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]

section Fibers

variable (Φ : J.Point.{w}) {A : Type uA} [Category.{vA} A]
  [HasColimitsOfSize.{w, w} A]

/-- Act on the actual colimit fiber by transporting the indexing fiber element. -/
def presheafFiberEnd (σ : AutGroup Φ) (P : Cᵒᵖ ⥤ A) :
    End (Φ.presheafFiber.obj P) :=
  End.of <| Φ.presheafFiberDesc (fun U x => Φ.toPresheafFiber U (σ.asIso.hom.app U x) P)
    (fun U V f x => by
      rw [Φ.toPresheafFiber_w]
      exact congrArg (fun y => Φ.toPresheafFiber V y P)
        (ConcreteCategory.congr_hom (σ.asIso.hom.naturality f) x).symm)

@[reassoc (attr := simp)]
theorem toPresheafFiber_presheafFiberEnd (σ : AutGroup Φ) (P : Cᵒᵖ ⥤ A)
    (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x P ≫ (presheafFiberEnd Φ σ P).asHom =
      Φ.toPresheafFiber U (σ.asIso.hom.app U x) P := by
  dsimp only [presheafFiberEnd]
  exact Φ.toPresheafFiber_presheafFiberDesc _ _ U x

@[simp]
theorem presheafFiberEnd_one (P : Cᵒᵖ ⥤ A) :
    (presheafFiberEnd Φ 1 P).asHom = 𝟙 _ := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  simp
  rfl

theorem presheafFiberEnd_mul (σ τ : AutGroup Φ) (P : Cᵒᵖ ⥤ A) :
    (presheafFiberEnd Φ (σ * τ) P).asHom =
      (presheafFiberEnd Φ τ P).asHom ≫ (presheafFiberEnd Φ σ P).asHom := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  simp
  rfl

@[reassoc]
theorem presheafFiberEnd_naturality (σ : AutGroup Φ)
    {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (presheafFiberEnd Φ σ P).asHom ≫ Φ.presheafFiber.map f =
      Φ.presheafFiber.map f ≫ (presheafFiberEnd Φ σ Q).asHom := by
  apply Φ.presheafFiber_hom_ext
  intro U x
  simp

end Fibers

section Modules

variable (Φ : J.Point.{w}) (R : Type w) [CommRing R]

/-- The representation on the actual module fiber of a presheaf. -/
def fiberRepresentation (P : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    Representation R (AutGroup Φ) ((Φ.presheafFiber (A := ModuleCat.{w} R)).obj P) where
  toFun σ := (presheafFiberEnd Φ σ P).asHom.hom
  map_one' := by
    rw [presheafFiberEnd_one]
    rfl
  map_mul' σ τ := by
    rw [presheafFiberEnd_mul]
    rfl

theorem fiberRepresentation_germ (P : Cᵒᵖ ⥤ ModuleCat.{w} R)
    (σ : AutGroup Φ) (U : C) (x : Φ.fiber.obj U) (s : P.obj (op U)) :
    fiberRepresentation Φ R P σ (Φ.toPresheafFiber U x P s) =
      Φ.toPresheafFiber U (σ.asIso.hom.app U x) P s :=
  ConcreteCategory.congr_hom (toPresheafFiber_presheafFiberEnd Φ σ P U x) s

/-- Maps of presheaves induce equivariant maps of their actual fibers. -/
def fiberIntertwiningMap {P Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : P ⟶ Q) :
    (fiberRepresentation Φ R P).IntertwiningMap (fiberRepresentation Φ R Q) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (Φ.presheafFiber.map f).hom
    (fun σ s => ConcreteCategory.congr_hom (presheafFiberEnd_naturality Φ σ f) s)

variable [LocallySmall.{w} C]

theorem fiberRepresentation_isSmooth (P : Cᵒᵖ ⥤ ModuleCat.{w} R) :
    Langlands.IsSmooth (fiberRepresentation Φ R P) := by
  intro s
  obtain ⟨U, x, t, rfl⟩ := Φ.toPresheafFiber_jointly_surjective s
  refine ⟨stabilizer Φ U x, ?_⟩
  intro σ
  change fiberRepresentation Φ R P σ.1 (Φ.toPresheafFiber U x P t) =
    Φ.toPresheafFiber U x P t
  rw [fiberRepresentation_germ]
  exact congrArg (fun y => Φ.toPresheafFiber U y P t) σ.2

/-- The actual fiber functor, lifted to smooth representations of point automorphisms. -/
def presheafSmoothFiber : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Langlands.SmoothRep.{w} R (AutGroup Φ) where
  obj P := Langlands.SmoothRep.of (fiberRepresentation Φ R P) (fiberRepresentation_isSmooth Φ R P)
  map f := Langlands.SmoothRep.ofHom (fiberIntertwiningMap Φ R f)
  map_id P := by
    apply ObjectProperty.hom_ext
    ext s
    exact ConcreteCategory.congr_hom (Φ.presheafFiber.map_id P) s
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext s
    exact ConcreteCategory.congr_hom (Φ.presheafFiber.map_comp f g) s

/-- Forgetting the action recovers the original presheaf fiber functor. -/
def presheafSmoothFiberForgetIso :
    presheafSmoothFiber Φ R ⋙ Langlands.SmoothRep.toRep ⋙
        forget₂ (Rep.{w} R (AutGroup Φ)) (ModuleCat.{w} R) ≅
      Φ.presheafFiber :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by rfl)

/-- The actual sheaf fiber, with its smooth point-automorphism action. -/
def sheafSmoothFiber : Sheaf J (ModuleCat.{w} R) ⥤ Langlands.SmoothRep.{w} R (AutGroup Φ) :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ presheafSmoothFiber Φ R

/-- Forgetting the smooth action on sheaf fibers recovers the original sheaf fiber. -/
def sheafSmoothFiberForgetIso :
    sheafSmoothFiber Φ R ⋙ Langlands.SmoothRep.toRep ⋙
        forget₂ (Rep.{w} R (AutGroup Φ)) (ModuleCat.{w} R) ≅
      Φ.sheafFiber :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by rfl)

end Modules

end Langlands.Sheaf.PointAutomorphisms
