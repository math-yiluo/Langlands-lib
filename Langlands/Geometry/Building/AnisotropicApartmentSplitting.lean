import Langlands.Geometry.Building.AnisotropicBuildingRealization
import Langlands.Geometry.Building.FullValidity.AffineApartment
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly

/-! # The actual affine apartment splitting for supplied anisotropic data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- Homomorphisms of commutative group schemes out of a split subtorus of an
anisotropic group are unique. -/
theorem IsAnisotropic.subsingleton_commHom_of_isSplitSubtorus
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i)
    (H : CommGroupScheme (Spec (CommRingCat.of k))) : Subsingleton (S ⟶ H) := by
  have := hG.subsingleton_hom_of_isSplitSubtorus hi H.toGrp
  exact ⟨fun f g => congrArg Additive.ofMul (Subsingleton.elim f.toMul g.toMul)⟩

/-- Such a split subtorus has only the zero cocharacter. -/
theorem IsAnisotropic.subsingleton_cocharacter_of_isSplitSubtorus
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i) :
    Subsingleton (cocharacterLattice S) := by
  have hid : (𝟙 S : S ⟶ S) = 0 :=
    (hG.subsingleton_commHom_of_isSplitSubtorus hi S).elim _ _
  have hz : ∀ ν : cocharacterLattice S, ν = 0 := by
    intro ν
    calc
      ν = ν ≫ 𝟙 S := (Category.comp_id ν).symm
      _ = ν ≫ 0 := by rw [hid]
      _ = 0 := by simp
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Its actual real cocharacter space is zero. -/
theorem IsAnisotropic.subsingleton_realTorusSpace_of_isSplitSubtorus
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i) : Subsingleton (V S) := by
  have := hG.subsingleton_cocharacter_of_isSplitSubtorus hi
  have hz : ∀ v : V S, v = 0 := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul r ν => rw [Subsingleton.elim ν 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun v w => (hz v).trans (hz w).symm⟩

/-- Every point of a split subtorus of an anisotropic group maps to the identity,
so its actual embedding is central. -/
theorem IsAnisotropic.isCentral_of_isSplitSubtorus
    (hG : IsAnisotropic G) (hi : IsSplitSubtorus i) : IsCentral i := by
  have hid : (𝟙 S : S ⟶ S) = 0 :=
    (hG.subsingleton_commHom_of_isSplitSubtorus hi S).elim _ _
  intro U x
  have hx := comp_groupHom_zero (H := S) x
  rw [← hid] at hx
  change x ≫ 𝟙 S.X = 1 at hx
  have hx1 : x = 1 := by simpa using hx
  rw [hx1, MonObj.one_comp]
  exact ((center G).carrier U).one_mem

/-- In an anisotropic group the actual maximal split torus is the split component. -/
theorem IsAnisotropic.isSplitComponent_of_isMaximalSplitTorus
    (hG : IsAnisotropic G) (hi : IsMaximalSplitTorus i) : IsSplitComponent i :=
  ⟨⟨hi.1, hG.isCentral_of_isSplitSubtorus hi.1⟩,
    fun A a ha f hf => hi.2 A a ha.1 f hf⟩

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- All existing Axiom 4.1.4 fields admit actual splitting data for an anisotropic
supplied parahoric building. The derived subgroup is the one in its zero datum. -/
theorem exists_apartmentSplitting_of_isAnisotropic (hG : IsAnisotropic G) :
    ∃ T : P.toValuationBuildingData.ApartmentSplitting, P.SatisfiesAffineApartmentAxiom T := by
  let D := P.zeroDatum.D
  let d : D ⟶ G := P.zeroDatum.d
  have hd : IsDerivedSubgroup d := P.zeroDatum.isSimplyConnectedDerivedCover.isDerivedSubgroup
  have hD := P.zeroDatum.isSimplyConnectedDerivedCover.isSimplyConnectedCover.isSemisimple
    |>.isConnectedReductive
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : Smooth D.X.hom := hD.smooth
  obtain ⟨S', j, hj⟩ := exists_maximalSplitTorus D
  have hjG : IsSplitSubtorus (j ≫ d) := hj.1.comp hd.1
  have hS : ∀ H : CommGroupScheme (Spec (CommRingCat.of F)), Subsingleton (P.S ⟶ H) :=
    fun H => hG.subsingleton_commHom_of_isSplitSubtorus P.isMaximalSplitTorus.1 H
  have hS' : ∀ H : CommGroupScheme (Spec (CommRingCat.of F)), Subsingleton (S' ⟶ H) :=
    fun H => hG.subsingleton_commHom_of_isSplitSubtorus hjG H
  let e : S' ≅ P.S :=
    { hom := 0
      inv := 0
      hom_inv_id := (hS' S').elim _ _
      inv_hom_id := (hS P.S).elim _ _ }
  let eG : S'.toGrp ≅ P.S.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg Additive.toMul e.hom_inv_id
      inv_hom_id := congrArg Additive.toMul e.inv_hom_id }
  let T : P.toValuationBuildingData.ApartmentSplitting :=
    { D := D
      d := d
      derivedTorus := S'
      j := j
      e := e.hom
      centralTorus := P.S
      a := 𝟙 P.S }
  have hv := hG.subsingleton_realTorusSpace_of_isSplitSubtorus P.isMaximalSplitTorus.1
  have hA := P.apartment.subsingleton_apartment_of_relativeRoots_eq_empty
    (hG.relativeRoots_eq_empty P.isMaximalSplitTorus.1)
  refine ⟨T, hd, hj, IsClosedSubgroup.of_iso eG, ?_, ?_, ?_, ?_, ?_,
    P.toValuationBuildingData.hasAffineConjugations⟩
  · exact (hG.subsingleton_hom_of_isSplitSubtorus hjG G).elim _ _
  · change IsSplitComponent (CommGroupScheme.groupHom (𝟙 P.S) ≫ P.i)
    change IsSplitComponent (𝟙 P.S.toGrp ≫ P.i)
    rw [Category.id_comp]
    exact hG.isSplitComponent_of_isMaximalSplitTorus P.isMaximalSplitTorus
  · have hb : LinearMap.range (cocharacterMapReal T.e) = ⊥ := Subsingleton.elim _ _
    have ht : LinearMap.range (cocharacterMapReal T.a) = ⊤ := Subsingleton.elim _ _
    rw [hb, ht]
    exact isCompl_bot_top
  · intro n
    exact ⟨Iso.refl S', (hS' P.S).elim _ _⟩
  · intro n _
    apply AffineEquiv.ext
    intro x
    exact hA.elim _ _

/-- A choice of actual anisotropic affine-apartment splitting from the original
parahoric zero datum. -/
def anisotropicApartmentSplitting (hG : IsAnisotropic G) :
    P.toValuationBuildingData.ApartmentSplitting :=
  Classical.choose (P.exists_apartmentSplitting_of_isAnisotropic hG)

/-- The chosen splitting satisfies exactly the published KP Axiom 4.1.4 predicate. -/
theorem satisfiesAffineApartmentAxiom_anisotropicApartmentSplitting (hG : IsAnisotropic G) :
    P.SatisfiesAffineApartmentAxiom (P.anisotropicApartmentSplitting hG) :=
  Classical.choose_spec (P.exists_apartmentSplitting_of_isAnisotropic hG)

end Langlands.Geometry.Building.ParahoricBuildingData
