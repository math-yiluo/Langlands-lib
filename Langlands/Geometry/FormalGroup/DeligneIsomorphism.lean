import Langlands.Geometry.FormalGroup.DeligneAdmissibility

/-! # Genuine isomorphisms and classes of Deligne's four sheaf data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X : TopCat.{u}} {F : Type u} [Field F] [Algebra O F]

/-- The actual scalar-restriction functor for total lattice sheaves. -/
def latticeScalarFunctor (d : ℕ) (π : O) (X : TopCat.{u}) :
    X.Sheaf (ModuleCat.{u} (PiAlgebra d π)) ⥤ X.Sheaf (ModuleCat.{u} O) :=
  sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (algebraMap O (PiAlgebra d π)))

omit [NeZero d] in
/-- Coefficient-linear maps commute with the actual distinguished Pi action. -/
theorem latticePi_naturality
    {M N : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))} (f : M ⟶ N) :
    latticePi d π X M ≫ (latticeScalarFunctor d π X).map f =
      (latticeScalarFunctor d π X).map f ≫ latticePi d π X N := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  exact (f.hom.app U).hom.map_smul (PiAlgebra.pi d π) x

namespace LatticePiSheaf

/-- Actual coefficient-linear maps together with maps of the homogeneous inclusions. -/
structure Hom (M N : LatticePiSheaf d π X) where
  total : M.sheaf ⟶ N.sheaf
  component (i : ZMod d) : M.component i ⟶ N.component i
  inclusion (i : ZMod d) :
    component i ≫ N.inclusion i =
      M.inclusion i ≫ (latticeScalarFunctor d π X).map total

omit [NeZero d] in
@[ext]
theorem Hom.ext {M N : LatticePiSheaf d π X} {f g : Hom M N}
    (ht : f.total = g.total) (hc : f.component = g.component) : f = g := by
  cases f
  cases g
  cases ht
  cases hc
  rfl

instance category : Category (LatticePiSheaf d π X) where
  Hom := Hom
  id M := {
    total := 𝟙 M.sheaf
    component i := 𝟙 (M.component i)
    inclusion i := by
      exact (Category.id_comp _).trans
        ((congrArg (fun k => M.inclusion i ≫ k)
          ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
            (Category.comp_id _)).symm }
  comp f g := {
    total := f.total ≫ g.total
    component i := f.component i ≫ g.component i
    inclusion i := by
      rw [Category.assoc, g.inclusion, ← Category.assoc, f.inclusion,
        Category.assoc, ← Functor.map_comp] }
  id_comp f := Hom.ext (Category.id_comp _) (by funext i; exact Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _) (by funext i; exact Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)
    (by funext i; exact Category.assoc _ _ _)

/-- Forget the homogeneous components, retaining the actual coefficient sheaf. -/
def totalFunctor :
    LatticePiSheaf d π X ⥤ X.Sheaf (ModuleCat.{u} (PiAlgebra d π)) where
  obj M := M.sheaf
  map f := f.total

/-- Taking each genuine homogeneous component is functorial. -/
def componentFunctor (i : ZMod d) :
    LatticePiSheaf d π X ⥤ X.Sheaf (ModuleCat.{u} O) where
  obj M := M.component i
  map f := f.component i

omit [NeZero d] in
/-- The homogeneous maps are determined by the map on the total sheaf. -/
theorem Hom.ext_total {M N : LatticePiSheaf d π X} {f g : M ⟶ N}
    (h : f.total = g.total) : f = g := by
  apply Hom.ext h
  funext i
  apply (cancel_mono (N.inclusion i)).mp
  rw [f.inclusion, g.inclusion, h]

omit [NeZero d] in
/-- Homogeneous maps automatically commute with the component Pi maps. -/
@[reassoc]
theorem Hom.pi_naturality {M N : LatticePiSheaf d π X} (f : M ⟶ N) (i : ZMod d) :
    M.pi i ≫ f.component (i + 1) = f.component i ≫ N.pi i := by
  apply (cancel_mono (N.inclusion (i + 1))).mp
  rw [Category.assoc, f.inclusion, ← Category.assoc, M.pi_inclusion,
    Category.assoc, latticePi_naturality, ← Category.assoc, ← f.inclusion,
    Category.assoc, ← N.pi_inclusion, Category.assoc]

end LatticePiSheaf

namespace FramedLatticePiSheaf

/-- Morphisms preserve the actual rational frame in degree zero. -/
structure Hom (M N : FramedLatticePiSheaf d π X F) where
  lattice : M.lattice ⟶ N.lattice
  frame : M.frame.hom ≫ (rationalSheafFunctor F X).map (lattice.component 0) =
    N.frame.hom

omit [NeZero d] in
@[ext]
theorem Hom.ext {M N : FramedLatticePiSheaf d π X F} {f g : Hom M N}
    (h : f.lattice = g.lattice) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance category : Category (FramedLatticePiSheaf d π X F) where
  Hom := Hom
  id M := {
    lattice := 𝟙 M.lattice
    frame := by
      change M.frame.hom ≫ (rationalSheafFunctor F X).map (𝟙 _) = _
      exact (congrArg (fun k => M.frame.hom ≫ k)
        ((rationalSheafFunctor F X).map_id (M.lattice.component 0))).trans
          (Category.comp_id _) }
  comp f g := {
    lattice := f.lattice ≫ g.lattice
    frame := by
      change _ ≫ (rationalSheafFunctor F X).map
        (f.lattice.component 0 ≫ g.lattice.component 0) = _
      rw [Functor.map_comp, ← Category.assoc, f.frame, g.frame] }
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

/-- Forget the frame while retaining the actual homogeneous lattice. -/
def latticeFunctor : FramedLatticePiSheaf d π X F ⥤ LatticePiSheaf d π X where
  obj M := M.lattice
  map f := f.lattice

end FramedLatticePiSheaf

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- Forgetting structural scalars retains injectivity of each genuine component inclusion. -/
instance structuralComponentInclusion_mono
    (M : GradedPiSheaf d S.sheaf (schemeScalar S (φ π))) (i : ZMod d) :
    Mono ((structuralOSheafFunctor S φ).map (M.componentInclusion i)) := by
  let : ∀ U, Mono
      (((sheafToPresheaf (Opens.grothendieckTopology S) (ModuleCat.{u} O)).map
        ((structuralOSheafFunctor S φ).map (M.componentInclusion i))).app U) :=
    fun U => (ModuleCat.mono_iff_injective _).mpr (fun _ _ h => Subtype.ext h)
  exact (sheafToPresheaf _ _).mono_of_mono_map (NatTrans.mono_of_mono_app _)

/-- Morphisms of the four data preserve eta, T, u and the rational frame. -/
structure Hom (D E : SheafPreDatum d π F φ) where
  eta : D.eta ⟶ E.eta
  tangent : D.tangent.graded ⟶ E.tangent.graded
  u : (latticeScalarFunctor d π (S : TopCat)).map eta.lattice.total ≫ E.u =
    D.u ≫ (structuralOSheafFunctor S φ).map tangent.val.val

@[ext]
theorem Hom.ext {D E : SheafPreDatum d π F φ} {f g : Hom D E}
    (he : f.eta = g.eta) (ht : f.tangent = g.tangent) : f = g := by
  cases f
  cases g
  cases he
  cases ht
  rfl

instance category : Category (SheafPreDatum d π F φ) where
  Hom := Hom
  id D := {
    eta := 𝟙 D.eta
    tangent := 𝟙 D.tangent.graded
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  comp f g := {
    eta := f.eta ≫ g.eta
    tangent := f.tangent ≫ g.tangent
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map
        (f.eta.lattice.total ≫ g.eta.lattice.total) ≫ _ =
          _ ≫ (structuralOSheafFunctor S φ).map
            (f.tangent.val.val ≫ g.tangent.val.val)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, g.u,
        ← Category.assoc, f.u, Category.assoc] }
  id_comp f := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Preservation of total u also preserves its specified homogeneous restrictions. -/
@[reassoc]
theorem Hom.uComponent_naturality {D E : SheafPreDatum d π F φ} (f : D ⟶ E)
    (i : ZMod d) :
    f.eta.lattice.component i ≫ E.uComponent i =
      D.uComponent i ≫ (structuralOSheafFunctor S φ).map (f.tangent.componentMap i) := by
  apply (cancel_mono
    ((structuralOSheafFunctor S φ).map (E.tangent.graded.componentInclusion i))).mp
  rw [Category.assoc, E.uComponent_inclusion, ← Category.assoc,
    f.eta.lattice.inclusion, Category.assoc, f.u, ← Category.assoc,
    ← D.uComponent_inclusion, Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← f.tangent.componentMap_inclusion, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The full data's eta forgetful functor retains its frame. -/
def etaFunctor : SheafPreDatum d π F φ ⥤ FramedLatticePiSheaf d π (S : TopCat) F where
  obj D := D.eta
  map f := f.eta

/-- The full data's T forgetful functor retains its grading and Pi operator. -/
def tangentFunctor :
    SheafPreDatum d π F φ ⥤ GradedPiSheaf d S.sheaf (schemeScalar S (φ π)) where
  obj D := D.tangent.graded
  map f := f.tangent

/-- An isomorphism of the four data identifies the actual tangent Pi-zero loci. -/
theorem piZeroLocus_eq_of_iso {D E : SheafPreDatum d π F φ} (e : D ≅ E) (i : ZMod d) :
    D.tangent.graded.piZeroLocus i = E.tangent.graded.piZeroLocus i :=
  GradedPiSheaf.piZeroLocus_eq_of_iso ((tangentFunctor).mapIso e) i

/-- Isomorphism means an actual invertible morphism preserving all four data. -/
def isoSetoid : Setoid (SheafPreDatum d π F φ) where
  r D E := Nonempty (D ≅ E)
  iseqv := ⟨fun D => ⟨CategoryTheory.Iso.refl D⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Isomorphism classes of the actual preliminary data. -/
def IsoClass := Quotient (isoSetoid (d := d) (π := π) (F := F) (φ := φ))

namespace IsoClass

/-- Send preliminary data to its actual isomorphism class. -/
def mk (D : SheafPreDatum d π F φ) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) := Quotient.mk _ D

/-- Equality of classes is precisely existence of a genuine isomorphism. -/
theorem mk_eq_mk_iff (D E : SheafPreDatum d π F φ) :
    mk D = mk E ↔ Nonempty (D ≅ E) :=
  Quotient.eq

end IsoClass

end SheafPreDatum

/-- Admissible four-data objects for the constructed three-condition predicate. -/
def SheafDatum (hπ : algebraMap O F π ≠ 0) :=
  {D : SheafPreDatum d π F φ // D.Admissible hπ}

namespace SheafDatum

variable (hπ : algebraMap O F π ≠ 0)

/-- Admissible objects are equivalent precisely when their four data are isomorphic. -/
def isoSetoid : Setoid (SheafDatum (d := d) (π := π) (F := F) (φ := φ) hπ) where
  r D E := Nonempty (D.val ≅ E.val)
  iseqv := ⟨fun D => ⟨CategoryTheory.Iso.refl D.val⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- Classes of actual admissible eta,T,u,r data on the fixed scheme. -/
def IsoClass := Quotient (isoSetoid (d := d) (π := π) (φ := φ) hπ)

namespace IsoClass

/-- Send admissible data to its actual isomorphism class. -/
def mk (D : SheafDatum (d := d) (π := π) (F := F) (φ := φ) hπ) :
    IsoClass (d := d) (π := π) (φ := φ) hπ := Quotient.mk _ D

/-- Equality of admissible classes is precisely isomorphism of their four data. -/
theorem mk_eq_mk_iff (D E : SheafDatum (d := d) (π := π) (F := F) (φ := φ) hπ) :
    mk hπ D = mk hπ E ↔ Nonempty (D.val ≅ E.val) :=
  Quotient.eq

/-- Forget admissibility on classes, retaining all four preliminary data. -/
def toPreliminary : IsoClass (d := d) (π := π) (φ := φ) hπ →
    SheafPreDatum.IsoClass (d := d) (π := π) (F := F) (φ := φ) :=
  Quotient.map (fun D => D.val) (fun _ _ h => h)

end IsoClass

end SheafDatum

/-- The constructed classes on each actual Nilp algebra. -/
def NilpSheafIsoClass (d : ℕ) [NeZero d] (π : O) (F : Type u) [Field F] [Algebra O F]
    (hπ : algebraMap O F π ≠ 0) (B : FormalGroup.Nilp.{u, u} O π) :=
  SheafDatum.IsoClass (d := d) (π := π) (φ := nilpGlobalScalar π B) hπ

end Langlands.DeligneFormalSpace
