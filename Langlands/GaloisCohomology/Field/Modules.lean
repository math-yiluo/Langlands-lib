import Langlands.ClassFieldTheory.Local.Cohomology
import Langlands.Cohomology.Profinite.SmoothCoefficients
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation

namespace Langlands.GaloisCohomology

open ClassFieldTheory.Local IntermediateField CategoryTheory

universe w u v

section IntRep

variable {G : Type v} [Monoid G]

def intRep {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) :
    Representation (ULift.{w} ℤ) G V where
  toFun g :=
    { toFun := φ g
      map_add' := map_add (φ g)
      map_smul' := fun r x => by
        change φ g (r.down • x) = r.down • φ g x
        exact map_zsmul (φ g) r.down x }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

@[simp]
theorem intRep_apply {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) (g : G) (x : V) :
    intRep.{w} φ g x = φ g x :=
  rfl

def intRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation (ULift.{w} ℤ) G (Additive M) :=
  intRep.{w} ((MulEquiv.monoidEnd M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem intRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    intRepOfMonoidEnd.{w} φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

def zRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation ℤ G (Additive M) :=
  (addMonoidEndRingEquivInt (Additive M) : AddMonoid.End (Additive M) →* _).comp
    ((MulEquiv.monoidEnd M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem zRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    zRepOfMonoidEnd φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

/-- An additive map as a `ULift ℤ`-linear map. -/
def uliftIntLinearMap {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    A →ₗ[ULift.{u} ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (r.down • x) = r.down • f x
    exact map_zsmul f r.down x

@[simp]
theorem uliftIntLinearMap_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (x : A) : uliftIntLinearMap.{u} f x = f x :=
  rfl

/-- An additive equivalence as a `ULift ℤ`-linear equivalence. -/
def uliftIntLinearEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    A ≃ₗ[ULift.{u} ℤ] B :=
  { uliftIntLinearMap.{u} e.toAddMonoidHom with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

@[simp]
theorem uliftIntLinearEquiv_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (x : A) : uliftIntLinearEquiv.{u} e x = e x :=
  rfl

end IntRep

section Galois

variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]

def galUnitsHom : Gal(L/K) →* Monoid.End Lˣ where
  toFun σ := Units.map (σ : L →* L)
  map_one' := by
    ext u
    rfl
  map_mul' σ τ := by
    ext u
    rfl

@[simp]
theorem coe_galUnitsHom_apply (σ : Gal(L/K)) (u : Lˣ) :
    ((galUnitsHom K L σ u : Lˣ) : L) = σ u :=
  rfl

def galRootsOfUnityHom (n : ℕ) : Gal(L/K) →* Monoid.End (rootsOfUnity n L) where
  toFun σ := restrictRootsOfUnity σ n
  map_one' := by
    ext ζ
    rfl
  map_mul' σ τ := by
    ext ζ
    rfl

@[simp]
theorem coe_galRootsOfUnityHom_apply (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) :=
  rfl

/-- The additive group of `L` with the Galois action, as a representation over `K`. -/
abbrev additiveModule : Rep.{u} K Gal(L/K) := Rep.ofDistribMulAction K Gal(L/K) L

/-- The multiplicative group `Lˣ` (written additively) with the Galois action: the Library's
`Langlands.ClassFieldTheory.Local.unitsRepresentation`. -/
abbrev unitsModule : Rep.{u} IntegerScalars.{u} Gal(L/K) := unitsRepresentation K L

/-- The group `μ_n(L)` of `n`-th roots of unity of `L` (written additively) with the Galois
action. -/
abbrev rootsOfUnityModule (n : ℕ) : Rep.{u} IntegerScalars.{u} Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{u} (galRootsOfUnityHom K L n))

/-- `Lˣ` with the Galois action, as a representation over the integers `ℤ` (for groups in the
universe of `ℤ`). -/
abbrev unitsModuleZ : Rep.{u} ℤ Gal(L/K) := Rep.of (zRepOfMonoidEnd (galUnitsHom K L))

abbrev rootsOfUnityModuleZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of (zRepOfMonoidEnd (galRootsOfUnityHom K L n))

variable {K L}

@[simp]
theorem additiveModule_ρ_apply (σ : Gal(L/K)) (x : L) : (additiveModule K L).ρ σ x = σ x :=
  rfl

@[simp]
theorem unitsModule_ρ_apply (σ : Gal(L/K)) (x : unitsModule K L) :
    (unitsModule K L).ρ σ x =
      (Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) : unitsModule K L) :=
  rfl

theorem coe_unitsModule_ρ_apply (σ : Gal(L/K)) (x : unitsModule K L) :
    ((Additive.toMul ((unitsModule K L).ρ σ x) : Lˣ) : L) = σ ((Additive.toMul x : Lˣ) : L) :=
  rfl

@[simp]
theorem unitsModuleZ_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (unitsModuleZ K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) :=
  rfl

@[simp]
theorem rootsOfUnityModule_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (rootsOfUnityModule K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl

@[simp]
theorem rootsOfUnityModuleZ_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (rootsOfUnityModuleZ K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) :=
  rfl

end Galois

end Langlands.GaloisCohomology
namespace Langlands.GaloisCohomology

open IntermediateField ClassFieldTheory.Local

universe w u

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

section Topology

variable (K L)

theorem galois_compactSpace [IsGalois K L] : CompactSpace Gal(L/K) :=
  inferInstance

theorem galois_t2Space [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  inferInstance

theorem galois_isProfinite [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end Topology

section Open

theorem apply_eq_of_mem_fixingSubgroup_adjoin {x : L} {σ : Gal(L/K)}
    (hσ : σ ∈ (K⟮x⟯).fixingSubgroup) : σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (mem_adjoin_simple_self K x)

theorem isOpen_of_forall_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K)) (x : L)
    (h : ∀ σ : Gal(L/K), σ x = x → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ))
    (fixingSubgroup_isOpen K⟮x⟯)

end Open

section Discrete

variable [Algebra.IsIntegral K L]

instance isSmoothRep_additiveModule : IsSmoothRep (additiveModule K L) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h

/-- The units module is smooth: the stabilizer of a unit is the Library's open subgroup
`unitOpenStabilizer`. -/
instance isSmoothRep_unitsModule : IsSmoothRep (unitsModule K L) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun x => by
    have h : (vectorStabilizer (unitsModule K L).ρ x : Set Gal(L/K)) =
        (unitOpenStabilizer K L x.toMul : Set Gal(L/K)) := by
      ext σ
      exact (mem_unitOpenStabilizer_iff K L x σ).symm
    rw [h]
    exact (unitOpenStabilizer K L x.toMul).isOpen

instance isSmoothRep_unitsModuleZ : IsSmoothRep (unitsModuleZ K L) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun x =>
    isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_vectorStabilizer, unitsModuleZ_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h

instance isSmoothRep_rootsOfUnityModule (n : ℕ) : IsSmoothRep (rootsOfUnityModule K L n) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_vectorStabilizer, rootsOfUnityModule_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)

instance isSmoothRep_rootsOfUnityModuleZ (n : ℕ) : IsSmoothRep (rootsOfUnityModuleZ K L n) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_vectorStabilizer, rootsOfUnityModuleZ_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)

end Discrete

section RootsOfUnity

variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L] (n : ℕ)

/-- The inclusion `μ_n(L) → Lˣ` as a morphism of Galois modules. -/
def rootsOfUnityToUnits : rootsOfUnityModule K L n ⟶ unitsModule K L :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive (rootsOfUnity n L).subtype) :
    Additive (rootsOfUnity n L) →ₗ[ULift.{u} ℤ] Additive Lˣ), fun σ => by
    ext x
    rfl⟩

@[simp]
theorem rootsOfUnityToUnits_hom_apply (x : Additive (rootsOfUnity n L)) :
    (rootsOfUnityToUnits K L n).hom x =
      (Additive.ofMul ((Additive.toMul x : rootsOfUnity n L) : Lˣ) : unitsModule K L) :=
  rfl

end RootsOfUnity

end Langlands.GaloisCohomology