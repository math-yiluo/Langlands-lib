import Langlands.Geometry.FormalGroup.DeligneFramedShift

/-! # Actual integer Pi paths and framed Deligne shifts -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X : TopCat.{u}} (F : Type u) [Field F] [Algebra O F]

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π X) (hπ : algebraMap O F π ≠ 0)

omit [NeZero d] in
/-- Equality of degrees gives the actual rational component transport. -/
@[reassoc]
theorem rationalTransport_inclusion {i j : ZMod d} (h : i = j) :
    (eqToIso (congrArg (M.rationalComponent F) h)).hom ≫ M.rationalInclusion F j =
      M.rationalInclusion F i := by
  subst j
  simp

omit [NeZero d] in
/-- Rational component transports commute with every genuine homogeneous lattice map. -/
@[reassoc]
theorem rationalTransport_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) {i j : ZMod d} (h : i = j) :
    (eqToIso (congrArg (M.rationalComponent F) h)).hom ≫
        (rationalSheafFunctor F X).map (f.component j) =
      (rationalSheafFunctor F X).map (f.component i) ≫
        (eqToIso (congrArg (N.rationalComponent F) h)).hom := by
  subst j
  exact (Category.id_comp _).trans (Category.comp_id _).symm

omit [NeZero d] in
/-- The positive return from a negative translate ends at its original degree. -/
theorem negativeReturn_degree (i : ZMod d) (n : ℕ) :
    i + (Int.negSucc n : ZMod d) + ((n + 1 : ℕ) : ZMod d) = i := by
  simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
  abel

/-- The positive return path from a negative translate ends in the original degree. -/
def rationalNegativeReturnIso (i : ZMod d) (n : ℕ) :
    M.rationalComponent F (i + (Int.negSucc n : ZMod d)) ≅
      M.rationalComponent F i :=
  M.rationalShiftIso F hπ (i + (Int.negSucc n : ZMod d)) (n + 1) ≪≫
    eqToIso (congrArg (M.rationalComponent F) (negativeReturn_degree i n))

/-- An arbitrary integer homogeneous Pi path, using the inverse positive return path
for a negative exponent. -/
def rationalPiIntIso (i : ZMod d) : (z : ℤ) →
    M.rationalComponent F i ≅ M.rationalComponent F (i + (z : ZMod d))
  | .ofNat n => M.rationalShiftIso F hπ i n ≪≫
      eqToIso (congrArg (M.rationalComponent F) (by simp))
  | .negSucc n => (M.rationalNegativeReturnIso F hπ i n).symm

/-- The return path is the restriction of the actual positive total power. -/
@[reassoc]
theorem rationalNegativeReturnIso_inclusion (i : ZMod d) (n : ℕ) :
    (M.rationalNegativeReturnIso F hπ i n).hom ≫ M.rationalInclusion F i =
      M.rationalInclusion F (i + (Int.negSucc n : ZMod d)) ≫
        (rationalPiAut F X d π M.sheaf hπ ^ (n + 1)).asIso.hom := by
  dsimp only [rationalNegativeReturnIso, Iso.trans_hom]
  rw [Category.assoc, M.rationalTransport_inclusion F (negativeReturn_degree i n),
    M.rationalShiftIso_inclusion F hπ]

/-- Every integer homogeneous path restricts the same integer power of the total Pi
isomorphism; this includes negative paths without assuming rational inclusions monic. -/
@[reassoc]
theorem rationalPiIntIso_inclusion (i : ZMod d) (z : ℤ) :
    (M.rationalPiIntIso F hπ i z).hom ≫ M.rationalInclusion F (i + (z : ZMod d)) =
      M.rationalInclusion F i ≫ (rationalPiAut F X d π M.sheaf hπ ^ z).asIso.hom := by
  cases z with
  | ofNat n =>
    dsimp only [rationalPiIntIso, Iso.trans_hom]
    rw [Category.assoc, M.rationalTransport_inclusion F (by simp)]
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
      M.rationalShiftIso_inclusion F hπ i n
  | negSucc n =>
    change (M.rationalNegativeReturnIso F hπ i n).inv ≫ _ = _
    apply (Iso.inv_comp_eq _).mpr
    rw [← Category.assoc, M.rationalNegativeReturnIso_inclusion F hπ]
    simp only [Category.assoc, zpow_negSucc, Aut.Aut_inv_def, Iso.symm_hom,
      Iso.hom_inv_id, Category.comp_id]

/-- Positive return paths commute with every genuine homogeneous lattice map. -/
@[reassoc]
theorem rationalNegativeReturnIso_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) (i : ZMod d) (n : ℕ) :
    (M.rationalNegativeReturnIso F hπ i n).hom ≫
        (rationalSheafFunctor F X).map (f.component i) =
      (rationalSheafFunctor F X).map
          (f.component (i + (Int.negSucc n : ZMod d))) ≫
        (N.rationalNegativeReturnIso F hπ i n).hom := by
  dsimp only [rationalNegativeReturnIso, Iso.trans_hom]
  rw [Category.assoc, rationalTransport_naturality F f (negativeReturn_degree i n),
    ← Category.assoc, rationalShiftIso_naturality F hπ, Category.assoc]

/-- Every integer rational Pi path is natural for genuine homogeneous lattice maps. -/
@[reassoc]
theorem rationalPiIntIso_naturality {M N : LatticePiSheaf d π X}
    (f : M ⟶ N) (i : ZMod d) (z : ℤ) :
    (M.rationalPiIntIso F hπ i z).hom ≫
        (rationalSheafFunctor F X).map (f.component (i + (z : ZMod d))) =
      (rationalSheafFunctor F X).map (f.component i) ≫
        (N.rationalPiIntIso F hπ i z).hom := by
  cases z with
  | ofNat n =>
    dsimp only [rationalPiIntIso, Iso.trans_hom]
    rw [Category.assoc, rationalTransport_naturality F f (by simp),
      ← Category.assoc, rationalShiftIso_naturality F hπ, Category.assoc]
  | negSucc n =>
    change (M.rationalNegativeReturnIso F hπ i n).inv ≫ _ =
      _ ≫ (N.rationalNegativeReturnIso F hπ i n).inv
    apply (Iso.inv_comp_eq _).mpr
    rw [← Category.assoc, rationalNegativeReturnIso_naturality F hπ,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

end LatticePiSheaf

/-- Taking the actual stalk carries every integer Pi power to the same stalk power. -/
theorem rationalPiStalkAut_zpow_hom
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (hπ : algebraMap O F π ≠ 0) (z : ℤ) (x : X) :
    (rationalPiStalkAut F X d π M hπ x ^ z).asIso.hom =
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
        (rationalPiAut F X d π M hπ ^ z).asIso.hom.hom := by
  let G := (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  exact congrArg (fun a => a.asIso.hom)
    ((G.mapAut _).map_zpow (rationalPiAut F X d π M hπ) z).symm

namespace FramedLatticePiSheaf

variable (M : FramedLatticePiSheaf d π X F) (hπ : algebraMap O F π ≠ 0)

/-- Shift the actual graded lattice and construct its rational frame by the integer Pi path. -/
def shiftInt (z : ℤ) : FramedLatticePiSheaf d π X F where
  lattice := M.lattice.shift (z : ZMod d)
  frame := M.frame ≪≫ M.lattice.rationalPiIntIso F hπ 0 z

/-- The actual framed shift acts on genuine frame-preserving homogeneous maps. -/
def shiftIntMap {M N : FramedLatticePiSheaf d π X F} (f : M ⟶ N) (z : ℤ) :
    M.shiftInt F hπ z ⟶ N.shiftInt F hπ z where
  lattice := LatticePiSheaf.shiftMap f.lattice (z : ZMod d)
  frame := by
    change (M.frame.hom ≫ (M.lattice.rationalPiIntIso F hπ 0 z).hom) ≫
        (rationalSheafFunctor F X).map (f.lattice.component (0 + (z : ZMod d))) =
      N.frame.hom ≫ (N.lattice.rationalPiIntIso F hπ 0 z).hom
    rw [Category.assoc, LatticePiSheaf.rationalPiIntIso_naturality F hπ,
      ← Category.assoc, f.frame]

/-- Integer framed shifts are functorial for the actual lattice-and-frame category. -/
def shiftIntFunctor (z : ℤ) :
    FramedLatticePiSheaf d π X F ⥤ FramedLatticePiSheaf d π X F where
  obj M := M.shiftInt F hπ z
  map f := shiftIntMap F hπ f z
  map_id _ := Hom.ext (LatticePiSheaf.Hom.ext_total rfl)
  map_comp _ _ := Hom.ext (LatticePiSheaf.Hom.ext_total rfl)

/-- In the unchanged total rational sheaf, the shifted frame is the original frame followed
by the actual total Pi power. -/
theorem frameToTotal_shiftInt (z : ℤ) :
    (M.shiftInt F hπ z).frameToTotal F =
      M.frameToTotal F ≫ (rationalPiAut F X d π M.lattice.sheaf hπ ^ z).asIso.hom := by
  change (M.frame.hom ≫ (M.lattice.rationalPiIntIso F hπ 0 z).hom) ≫
      M.lattice.rationalInclusion F (0 + (z : ZMod d)) = _
  rw [Category.assoc, M.lattice.rationalPiIntIso_inclusion F hπ, ← Category.assoc]
  rfl

/-- The shifted frame on the actual stalk is the original frame followed by Pi^z. -/
theorem frameStalkMap_shiftInt (z : ℤ) (x : X) :
    (M.shiftInt F hπ z).frameStalkMap F x =
      M.frameStalkMap F x ≫
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ z).asIso.hom := by
  unfold frameStalkMap
  rw [M.frameToTotal_shiftInt F hπ z]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
  rw [rationalPiStalkAut_zpow_hom]
  dsimp only [shiftInt, LatticePiSheaf.shift, TopCat.Presheaf.Γgerm]
  rw [← TopCat.Presheaf.stalkFunctor_map_germ]

/-- O-valued shifted frame vectors are carried by the actual Pi^z stalk map. -/
theorem integralFrameStalkMap_shiftInt (z : ℤ) (x : X) :
    (M.shiftInt F hπ z).integralFrameStalkMap F x =
      (((ModuleCat.restrictScalars (algebraMap O F)).map
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ z).asIso.hom).hom).comp
          (M.integralFrameStalkMap F x) := by
  apply LinearMap.ext
  intro v
  exact congrArg (fun k => k (fun j => algebraMap O F (v j)))
    (M.frameStalkMap_shiftInt F hπ z x)

/-- The actual integral frame lattice of the integer shift is its old Pi^z translate. -/
theorem frameStalkLattice_shiftInt (z : ℤ) (x : X) :
    (M.shiftInt F hπ z).frameStalkLattice F x =
      M.translatedFrameStalkLattice F hπ z x := by
  unfold frameStalkLattice translatedFrameStalkLattice
  rw [M.integralFrameStalkMap_shiftInt F hπ z x, LinearMap.range_comp]
  rfl

/-- Every integer translate of the shifted frame is the corresponding old translate. -/
theorem translatedFrameStalkLattice_shiftInt (z : ℤ) (i : ℤ) (x : X) :
    (M.shiftInt F hπ z).translatedFrameStalkLattice F hπ i x =
      M.translatedFrameStalkLattice F hπ (i + z) x := by
  have hp :
      (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ (i + z)).asIso.hom =
        (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ z).asIso.hom ≫
          (rationalPiStalkAut F X d π M.lattice.sheaf hπ x ^ i).asIso.hom := by
    rw [zpow_add]
    rfl
  unfold translatedFrameStalkLattice
  rw [M.frameStalkLattice_shiftInt F hπ z x]
  unfold translatedFrameStalkLattice
  rw [← Submodule.map_comp, hp, Functor.map_comp]
  rfl

/-- Raw integer shifts change the literal normalized determinant by pi^z. -/
theorem normalizedFrameDeterminant_shiftInt (z : ℤ) (i : ℤ) (x : X) :
    (M.shiftInt F hπ z).normalizedFrameDeterminant F hπ i x =
      scaleStalkLattice F (algebraMap O F π ^ z) _
        (M.normalizedFrameDeterminant F hπ (i + z) x) := by
  unfold normalizedFrameDeterminant
  rw [M.translatedFrameStalkLattice_shiftInt F hπ z i x, scaleStalkLattice_mul]
  congr 1
  rw [← zpow_add₀ hπ]
  congr 1
  omega

end FramedLatticePiSheaf

variable {F} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (hπ : algebraMap O F π ≠ 0)

/-- Shift all four actual data, with the rational frame constructed by the integer Pi path. -/
def shiftInt (z : ℤ) : SheafPreDatum d π F φ where
  eta := D.eta.shiftInt F hπ z
  tangent := D.tangent.shift (z : ZMod d)
  u := D.u
  uPi := D.uPi
  uComponent i := D.uComponent (i + (z : ZMod d))
  uComponent_inclusion i := D.uComponent_inclusion (i + (z : ZMod d))
  locallyGenerates := D.locallyGenerates

/-- The actual total residue-fibre map is unchanged by simultaneous degree translation. -/
@[simp]
theorem piQuotientResidueMap_shiftInt (z : ℤ) (x : S) :
    (D.shiftInt hπ z).piQuotientResidueMap x = D.piQuotientResidueMap x := rfl

/-- The total residue-fibre injectivity condition is preserved in both directions. -/
@[simp]
theorem residueFibreInjective_shiftInt_iff (z : ℤ) :
    (D.shiftInt hπ z).ResidueFibreInjective ↔ D.ResidueFibreInjective := Iff.rfl

/-- The actual tangent Pi-zero loci translate by the same cyclic degree. -/
theorem piZeroLocus_shiftInt (z : ℤ) (i : ZMod d) :
    (D.shiftInt hπ z).tangent.graded.piZeroLocus i =
      D.tangent.graded.piZeroLocus (i + (z : ZMod d)) :=
  D.tangent.graded.piZeroLocus_shift (z : ZMod d) i

/-- The actual component determinant translates by the same cyclic degree. -/
theorem componentDeterminant_shiftInt (z : ℤ) (i : ZMod d) (x : S) :
    (D.shiftInt hπ z).componentDeterminant i x =
      D.componentDeterminant (i + (z : ZMod d)) x := rfl

/-- Condition (a) is preserved by the actual simultaneous grading translation. -/
theorem constantOnPiZeroLoci_shiftInt_iff (z : ℤ) :
    (D.shiftInt hπ z).ConstantOnPiZeroLoci ↔ D.ConstantOnPiZeroLoci := by
  let C (Z : Set S) (A : (S : TopCat).Sheaf (ModuleCat.{u} O)) : Prop :=
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{u} O)
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        ContinuousMap Z S))).obj A ≅
          (constantSheaf (Opens.grothendieckTopology (TopCat.of Z))
            (ModuleCat.{u} O)).obj (ModuleCat.of O (Fin d → O)))
  change (∀ i, C ((D.shiftInt hπ z).tangent.graded.piZeroLocus i)
      ((D.shiftInt hπ z).eta.lattice.component i)) ↔
    ∀ i, C (D.tangent.graded.piZeroLocus i) (D.eta.lattice.component i)
  have hc (i : ZMod d) :
      C ((D.shiftInt hπ z).tangent.graded.piZeroLocus i)
          ((D.shiftInt hπ z).eta.lattice.component i) =
        C (D.tangent.graded.piZeroLocus (i + (z : ZMod d)))
          (D.eta.lattice.component (i + (z : ZMod d))) := by
    change C ((D.shiftInt hπ z).tangent.graded.piZeroLocus i)
      (D.eta.lattice.component (i + (z : ZMod d))) = _
    rw [D.piZeroLocus_shiftInt hπ z]
  simp only [hc]
  constructor
  · intro h i
    simpa only [sub_add_cancel] using h (i - (z : ZMod d))
  · intro h i
    exact h (i + (z : ZMod d))

/-- Condition (c) after a raw shift includes the explicitly computed pi^z correction. -/
theorem determinantNormalized_shiftInt_iff (z : ℤ) :
    (D.shiftInt hπ z).DeterminantNormalized hπ ↔
      ∀ (i : ℤ) (x : S),
        x ∈ D.tangent.graded.piZeroLocus ((i + z : ℤ) : ZMod d) →
          D.componentDeterminant ((i + z : ℤ) : ZMod d) x =
            scaleStalkLattice F (algebraMap O F π ^ z) _
              (D.eta.normalizedFrameDeterminant F hπ (i + z) x) := by
  have hf (i : ℤ) (x : S) :
      (D.shiftInt hπ z).eta.normalizedFrameDeterminant F hπ i x =
        scaleStalkLattice F (algebraMap O F π ^ z) _
          (D.eta.normalizedFrameDeterminant F hπ (i + z) x) :=
    D.eta.normalizedFrameDeterminant_shiftInt F hπ z i x
  unfold DeterminantNormalized
  simp only [D.piZeroLocus_shiftInt hπ z, D.componentDeterminant_shiftInt hπ z,
    hf, Int.cast_add]

/-- A genuine morphism of four data gives a genuine morphism of the constructed shifts. -/
def shiftIntMap {D E : SheafPreDatum d π F φ} (f : D ⟶ E) (z : ℤ) :
    D.shiftInt hπ z ⟶ E.shiftInt hπ z where
  eta := FramedLatticePiSheaf.shiftIntMap F hπ f.eta z
  tangent := GradedPiSheaf.shiftMap f.tangent (z : ZMod d)
  u := f.u

/-- Simultaneous integer shifts form a functor on the actual four-data category. -/
def shiftIntFunctor (z : ℤ) :
    SheafPreDatum d π F φ ⥤ SheafPreDatum d π F φ where
  obj D := D.shiftInt hπ z
  map f := shiftIntMap hπ f z
  map_id _ := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total rfl)) (GradedPiSheaf.Hom.ext rfl)
  map_comp _ _ := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total rfl)) (GradedPiSheaf.Hom.ext rfl)

/-- The preliminary classes shift through genuine isomorphisms of all four data. -/
def IsoClass.shiftInt (z : ℤ) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) →
      IsoClass (d := d) (π := π) (F := F) (φ := φ) :=
  Quotient.map (fun D => D.shiftInt hπ z)
    (fun _ _ ⟨e⟩ => ⟨(shiftIntFunctor hπ z).mapIso e⟩)

end SheafPreDatum

end Langlands.DeligneFormalSpace
