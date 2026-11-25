import Langlands.Geometry.FormalGroup.DeligneGradingShift
import Langlands.Geometry.FormalGroup.DeligneHomogeneousPi
import Langlands.Geometry.FormalGroup.DeligneFrameDeterminant

/-! # Actual rational frames on shifted Deligne sheaf data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X : TopCat.{u}} (F : Type u) [Field F] [Algebra O F]

namespace LatticePiSheaf

omit [NeZero d] in
/-- Component maps commute with actual transports between equal degree indices. -/
@[reassoc]
theorem Hom.component_transport_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) {i j : ZMod d} (h : i = j) :
    eqToHom (congrArg M.component h) ≫ f.component j =
      f.component i ≫ eqToHom (congrArg N.component h) := by
  subst j
  simp

omit [NeZero d] in
/-- Genuine homogeneous lattice maps commute with every actual positive Pi iterate. -/
@[reassoc]
theorem Hom.piIterate_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) (i : ZMod d) (n : ℕ) :
    M.piIterate i n ≫ f.component (i + (n : ZMod d)) =
      f.component i ≫ N.piIterate i n := by
  induction n with
  | zero => exact f.component_transport_naturality (by simp)
  | succ n ih =>
    simp only [piIterate, Category.assoc]
    rw [f.component_transport_naturality, ← Category.assoc (M.pi _),
      f.pi_naturality, Category.assoc, ← Category.assoc, ih, Category.assoc]
    simp [Nat.cast_add, add_assoc]

variable (M : LatticePiSheaf d π X) (hπ : algebraMap O F π ≠ 0)

/-- The actual rational Pi path identifies a component with the corresponding shifted one. -/
def rationalShiftIso (i : ZMod d) (n : ℕ) :
    M.rationalComponent F i ≅ (M.shift (n : ZMod d)).rationalComponent F i :=
  M.rationalPiIterateIso F hπ i n

/-- The rationalized actual iterates are natural for genuine homogeneous lattice maps. -/
@[reassoc]
theorem rationalShiftIso_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) (i : ZMod d) (n : ℕ) :
    (M.rationalShiftIso F hπ i n).hom ≫
        (rationalSheafFunctor F X).map (f.component (i + (n : ZMod d))) =
      (rationalSheafFunctor F X).map (f.component i) ≫
        (N.rationalShiftIso F hπ i n).hom := by
  dsimp only [rationalShiftIso]
  rw [M.rationalPiIterateIso_hom F hπ, N.rationalPiIterateIso_hom F hπ,
    ← Functor.map_comp, f.piIterate_naturality, Functor.map_comp]

/-- Powers of the actual total rational automorphism are rationalized integral powers. -/
theorem rationalPiAut_pow_hom (n : ℕ) :
    (rationalPiAut F X d π M.sheaf hπ ^ n).asIso.hom =
      (rationalSheafFunctor F X).map (End.of (latticePi d π X M.sheaf) ^ n).asHom := by
  change (Aut.toEnd (rationalPiAut F X d π M.sheaf hπ ^ n)).asHom = _
  rw [map_pow]
  change (End.of (rationalPiAut F X d π M.sheaf hπ).asIso.hom ^ n).asHom = _
  rw [rationalPiAut_hom]
  exact congrArg End.asHom ((Functor.mapEnd _ (rationalSheafFunctor F X)).map_pow
    (End.of (latticePi d π X M.sheaf)) n).symm

/-- The constructed component path is exactly the restriction of the actual total power. -/
@[reassoc]
theorem rationalShiftIso_inclusion (i : ZMod d) (n : ℕ) :
    (M.rationalShiftIso F hπ i n).hom ≫
        M.rationalInclusion F (i + (n : ZMod d)) =
      M.rationalInclusion F i ≫ (rationalPiAut F X d π M.sheaf hπ ^ n).asIso.hom := by
  dsimp only [rationalShiftIso, rationalInclusion]
  rw [M.rationalPiIterateIso_hom F hπ, ← Functor.map_comp, M.piIterate_inclusion,
    Functor.map_comp, M.rationalPiAut_pow_hom F hπ]

end LatticePiSheaf

/-- Taking the actual stalk carries a positive total Pi power to the same stalk power. -/
theorem rationalPiStalkAut_natCast_hom
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) (n : ℕ) (x : X) :
    (rationalPiStalkAut F X d π M hπ x ^ (n : ℤ)).asIso.hom =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
        (rationalPiAut F X d π M hπ ^ n).asIso.hom.hom := by
  rw [zpow_natCast]
  let G := (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  exact congrArg (fun a => a.asIso.hom)
    ((G.mapAut _).map_pow (rationalPiAut F X d π M hπ) n).symm

namespace FramedLatticePiSheaf

variable (M : FramedLatticePiSheaf d π X F) (hπ : algebraMap O F π ≠ 0)

/-- Shift the actual graded lattice and construct its rational frame by the positive Pi path. -/
def shiftNat (n : ℕ) : FramedLatticePiSheaf d π X F where
  lattice := M.lattice.shift (n : ZMod d)
  frame := M.frame ≪≫ M.lattice.rationalShiftIso F hπ 0 n

/-- The actual framed shift acts on genuine frame-preserving homogeneous maps. -/
def shiftNatMap {M N : FramedLatticePiSheaf d π X F} (f : M ⟶ N) (n : ℕ) :
    M.shiftNat F hπ n ⟶ N.shiftNat F hπ n where
  lattice := LatticePiSheaf.shiftMap f.lattice (n : ZMod d)
  frame := by
    change (M.frame.hom ≫ (M.lattice.rationalShiftIso F hπ 0 n).hom) ≫
        (rationalSheafFunctor F X).map (f.lattice.component (0 + (n : ZMod d))) =
      N.frame.hom ≫ (N.lattice.rationalShiftIso F hπ 0 n).hom
    rw [Category.assoc, LatticePiSheaf.rationalShiftIso_naturality F hπ,
      ← Category.assoc, f.frame]

/-- Positive framed shifts are functorial for the actual lattice-and-frame category. -/
def shiftNatFunctor (n : ℕ) :
    FramedLatticePiSheaf d π X F ⥤ FramedLatticePiSheaf d π X F where
  obj M := M.shiftNat F hπ n
  map f := shiftNatMap F hπ f n
  map_id _ := Hom.ext (LatticePiSheaf.Hom.ext_total rfl)
  map_comp _ _ := Hom.ext (LatticePiSheaf.Hom.ext_total rfl)

/-- In the unchanged total rational sheaf, the shifted frame is the original frame followed
by the actual total Pi power. -/
theorem frameToTotal_shiftNat (n : ℕ) :
    (M.shiftNat F hπ n).frameToTotal F =
      M.frameToTotal F ≫ (rationalPiAut F X d π M.lattice.sheaf hπ ^ n).asIso.hom := by
  change (M.frame.hom ≫ (M.lattice.rationalShiftIso F hπ 0 n).hom) ≫
      M.lattice.rationalInclusion F (0 + (n : ZMod d)) = _
  rw [Category.assoc, M.lattice.rationalShiftIso_inclusion F hπ, ← Category.assoc]
  rfl

/-- The shifted frame on the actual stalk is the original frame followed by Pi^n. -/
theorem frameStalkMap_shiftNat (n : ℕ) (x : X) :
    (M.shiftNat F hπ n).frameStalkMap F x =
      M.frameStalkMap F x ≫
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ (n : ℤ)).asIso.hom := by
  unfold frameStalkMap
  rw [M.frameToTotal_shiftNat F hπ n]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  rw [rationalPiStalkAut_natCast_hom]
  dsimp only [shiftNat, LatticePiSheaf.shift, TopCat.Presheaf.Γgerm]
  rw [← TopCat.Presheaf.stalkFunctor_map_germ]

/-- O-valued shifted frame vectors are carried by the actual Pi^n stalk map. -/
theorem integralFrameStalkMap_shiftNat (n : ℕ) (x : X) :
    (M.shiftNat F hπ n).integralFrameStalkMap F x =
      (((ModuleCat.restrictScalars (algebraMap O F)).map
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ (n : ℤ)).asIso.hom).hom).comp
          (M.integralFrameStalkMap F x) := by
  apply LinearMap.ext
  intro v
  exact congrArg (fun k => k (fun j => algebraMap O F (v j)))
    (M.frameStalkMap_shiftNat F hπ n x)

/-- The actual integral frame lattice of the positive shift is its old Pi^n translate. -/
theorem frameStalkLattice_shiftNat (n : ℕ) (x : X) :
    (M.shiftNat F hπ n).frameStalkLattice F x =
      M.translatedFrameStalkLattice F hπ (n : ℤ) x := by
  unfold frameStalkLattice translatedFrameStalkLattice
  rw [M.integralFrameStalkMap_shiftNat F hπ n x, LinearMap.range_comp]
  rfl

/-- Every integer translate of the shifted frame is the corresponding old translate. -/
theorem translatedFrameStalkLattice_shiftNat (n : ℕ) (i : ℤ) (x : X) :
    (M.shiftNat F hπ n).translatedFrameStalkLattice F hπ i x =
      M.translatedFrameStalkLattice F hπ (i + (n : ℤ)) x := by
  have hp :
      (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ (i + (n : ℤ))).asIso.hom =
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ (n : ℤ)).asIso.hom ≫
          (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ i).asIso.hom := by
    rw [zpow_add]
    rfl
  unfold translatedFrameStalkLattice
  rw [M.frameStalkLattice_shiftNat F hπ n x]
  unfold translatedFrameStalkLattice
  rw [← Submodule.map_comp, hp, Functor.map_comp]
  rfl

/-- Raw positive shifts change the literal normalized determinant by pi^n. -/
theorem normalizedFrameDeterminant_shiftNat (n : ℕ) (i : ℤ) (x : X) :
    (M.shiftNat F hπ n).normalizedFrameDeterminant F hπ i x =
      scaleStalkLattice F (algebraMap O F π ^ n) _
        (M.normalizedFrameDeterminant F hπ (i + (n : ℤ)) x) := by
  unfold normalizedFrameDeterminant
  rw [M.translatedFrameStalkLattice_shiftNat F hπ n i x, scaleStalkLattice_mul]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ hπ]
  congr 1
  omega

end FramedLatticePiSheaf

variable {F} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (hπ : algebraMap O F π ≠ 0)

/-- Shift all four actual data, with the rational frame constructed by the positive Pi path. -/
def shiftNat (n : ℕ) : SheafPreDatum d π F φ where
  eta := D.eta.shiftNat F hπ n
  tangent := D.tangent.shift (n : ZMod d)
  u := D.u
  uPi := D.uPi
  uComponent i := D.uComponent (i + (n : ZMod d))
  uComponent_inclusion i := D.uComponent_inclusion (i + (n : ZMod d))
  locallyGenerates := D.locallyGenerates

/-- The actual total residue-fibre map is unchanged by simultaneous degree translation. -/
@[simp]
theorem piQuotientResidueMap_shiftNat (n : ℕ) (x : S) :
    (D.shiftNat hπ n).piQuotientResidueMap x = D.piQuotientResidueMap x := rfl

/-- The total residue-fibre injectivity condition is preserved in both directions. -/
@[simp]
theorem residueFibreInjective_shiftNat_iff (n : ℕ) :
    (D.shiftNat hπ n).ResidueFibreInjective ↔ D.ResidueFibreInjective := Iff.rfl

/-- The actual tangent Pi-zero loci translate by the same cyclic degree. -/
theorem piZeroLocus_shiftNat (n : ℕ) (i : ZMod d) :
    (D.shiftNat hπ n).tangent.graded.piZeroLocus i =
      D.tangent.graded.piZeroLocus (i + (n : ZMod d)) :=
  D.tangent.graded.piZeroLocus_shift (n : ZMod d) i

/-- The actual component determinant translates by the same cyclic degree. -/
theorem componentDeterminant_shiftNat (n : ℕ) (i : ZMod d) (x : S) :
    (D.shiftNat hπ n).componentDeterminant i x =
      D.componentDeterminant (i + (n : ZMod d)) x := rfl

/-- Condition (a) is preserved by the actual simultaneous grading translation. -/
theorem constantOnPiZeroLoci_shiftNat_iff (n : ℕ) :
    (D.shiftNat hπ n).ConstantOnPiZeroLoci ↔ D.ConstantOnPiZeroLoci := by
  let C (Z : Set S) (A : (S : TopCat).Sheaf (ModuleCat.{u} O)) : Prop :=
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{u} O)
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        ContinuousMap Z S))).obj A ≅
          (constantSheaf (Opens.grothendieckTopology (TopCat.of Z))
            (ModuleCat.{u} O)).obj (ModuleCat.of O (Fin d → O)))
  change (∀ i, C ((D.shiftNat hπ n).tangent.graded.piZeroLocus i)
      ((D.shiftNat hπ n).eta.lattice.component i)) ↔
    ∀ i, C (D.tangent.graded.piZeroLocus i) (D.eta.lattice.component i)
  have hc (i : ZMod d) :
      C ((D.shiftNat hπ n).tangent.graded.piZeroLocus i)
          ((D.shiftNat hπ n).eta.lattice.component i) =
        C (D.tangent.graded.piZeroLocus (i + (n : ZMod d)))
          (D.eta.lattice.component (i + (n : ZMod d))) := by
    change C ((D.shiftNat hπ n).tangent.graded.piZeroLocus i)
      (D.eta.lattice.component (i + (n : ZMod d))) = _
    rw [D.piZeroLocus_shiftNat hπ n]
  simp only [hc]
  constructor
  · intro h i
    simpa only [sub_add_cancel] using h (i - (n : ZMod d))
  · intro h i
    exact h (i + (n : ZMod d))

/-- Condition (c) after a raw shift includes the explicitly computed pi^n correction. -/
theorem determinantNormalized_shiftNat_iff (n : ℕ) :
    (D.shiftNat hπ n).DeterminantNormalized hπ ↔
      ∀ (i : ℤ) (x : S),
        x ∈ D.tangent.graded.piZeroLocus ((i + (n : ℤ) : ℤ) : ZMod d) →
          D.componentDeterminant ((i + (n : ℤ) : ℤ) : ZMod d) x =
            scaleStalkLattice F (algebraMap O F π ^ n) _
              (D.eta.normalizedFrameDeterminant F hπ (i + (n : ℤ)) x) := by
  have hf (i : ℤ) (x : S) :
      (D.shiftNat hπ n).eta.normalizedFrameDeterminant F hπ i x =
        scaleStalkLattice F (algebraMap O F π ^ n) _
          (D.eta.normalizedFrameDeterminant F hπ (i + (n : ℤ)) x) :=
    D.eta.normalizedFrameDeterminant_shiftNat F hπ n i x
  unfold DeterminantNormalized
  simp only [D.piZeroLocus_shiftNat hπ n, D.componentDeterminant_shiftNat hπ n,
    hf, Int.cast_add, Int.cast_natCast]

/-- A genuine morphism of four data gives a genuine morphism of the constructed shifts. -/
def shiftNatMap {D E : SheafPreDatum d π F φ} (f : D ⟶ E) (n : ℕ) :
    D.shiftNat hπ n ⟶ E.shiftNat hπ n where
  eta := FramedLatticePiSheaf.shiftNatMap F hπ f.eta n
  tangent := GradedPiSheaf.shiftMap f.tangent (n : ZMod d)
  u := f.u

/-- Simultaneous positive shifts form a functor on the actual four-data category. -/
def shiftNatFunctor (n : ℕ) :
    SheafPreDatum d π F φ ⥤ SheafPreDatum d π F φ where
  obj D := D.shiftNat hπ n
  map f := shiftNatMap hπ f n
  map_id _ := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total rfl)) (GradedPiSheaf.Hom.ext rfl)
  map_comp _ _ := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total rfl)) (GradedPiSheaf.Hom.ext rfl)

/-- The preliminary classes shift through genuine isomorphisms of all four data. -/
def IsoClass.shiftNat (n : ℕ) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) →
      IsoClass (d := d) (π := π) (F := F) (φ := φ) :=
  Quotient.map (fun D => D.shiftNat hπ n)
    (fun _ _ ⟨e⟩ => ⟨(shiftNatFunctor hπ n).mapIso e⟩)

end SheafPreDatum

end Langlands.DeligneFormalSpace
