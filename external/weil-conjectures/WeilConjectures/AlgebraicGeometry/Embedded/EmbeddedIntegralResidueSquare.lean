/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # The constant and residue squares of an integral coefficient isomorphism

Source: Stacks Tag 09C1 and the integral-model coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] Sheaf.monoidalCategory

private def ringSheafMap
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {S T : Sheaf J RingCat.{u + 1}}
    (f : (sheafCompose J (forget₂ RingCat Ab)).obj S ⟶
      (sheafCompose J (forget₂ RingCat Ab)).obj T) [IsMonHom f] : S ⟶ T := by
  let A := (sheafCompose J (forget₂ RingCat Ab)).obj S
  let B := (sheafCompose J (forget₂ RingCat Ab)).obj T
  have hS : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      S.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := S.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  have hT : (sheafToPresheaf J Ab.{u + 1}).monObjObj B =
      T.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj B.obj := T.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul B
  have hf : IsMonHom ((sheafToPresheaf J Ab.{u + 1}).map f) := inferInstance
  rw [hS, hT] at hf
  letI : MonObj A.obj := S.obj.monObjCompForget₂
  letI : MonObj B.obj := T.obj.monObjCompForget₂
  letI : IsMonHom f.hom := hf
  refine ⟨{ app := fun U ↦ ?_, naturality := ?_ }⟩
  · rename_i U
    refine RingCat.ofHom { (f.hom.app U).hom with map_one' := ?_, map_mul' := ?_ }
    · have h := ConcreteCategory.congr_hom
        (congr_app (IsMonHom.one_hom f.hom) U) (ULift.up 1)
      change (f.hom.app U) ((1 : ℤ) : S.obj.obj U) = ((1 : ℤ) : T.obj.obj U) at h
      simp only [Int.cast_one] at h
      change (f.hom.app U) (1 : S.obj.obj U) = (1 : T.obj.obj U)
      exact h
    · intro a b
      exact ConcreteCategory.congr_hom
        (congr_app (IsMonHom.mul_hom f.hom) U) (a ⊗ₜ[ℤ] b)
  · intro U V g
    apply RingCat.hom_ext
    ext x
    exact ConcreteCategory.congr_hom (f.hom.naturality g) x

private def pointEquiv (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] : R ≃+* ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, R) :=
  { toFun := fun a ↦ ULift.up (ContinuousMap.const _ a)
    invFun := fun a ↦ a.down PUnit.unit
    left_inv := fun _ ↦ rfl
    right_inv := fun a ↦ by
      apply ULift.ext
      ext x
      cases x
      rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl }

set_option backward.isDefEq.respectTransparency.types false in
private theorem constantSquare
    (A B : CommRingCat.{u + 1}) (f : A ⟶ B)
    {S T : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}}
    (g : S ⟶ T)
    (a : (Functor.const Profinite.{u}ᵒᵖ).obj
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj A) ⟶ S.obj)
    (b : (Functor.const Profinite.{u}ᵒᵖ).obj
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj B) ⟶ T.obj)
    (h : (Functor.const Profinite.{u}ᵒᵖ).map
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map f) ≫ b = a ≫ g.hom) :
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf _ CommRingCat.{u + 1}).map f) ≫
      ((constantCommuteCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app B).hom ≫
        ((sheafificationAdjunction _ RingCat.{u + 1}).homEquiv _ _).symm b =
      ((constantCommuteCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app A).hom ≫
        ((sheafificationAdjunction _ RingCat.{u + 1}).homEquiv _ _).symm a ≫ g := by
  let J := coherentTopology Profinite.{u}
  let U := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let c := constantCommuteCompose J U
  erw [← Category.assoc, c.hom.naturality f, Category.assoc]
  congr 1
  exact (sheafificationAdjunction J RingCat.{u + 1}).homEquiv_naturality_right_square
    ((Functor.const Profinite.{u}ᵒᵖ).map (U.map f)) b a g h

private def ringSheafIso
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    {S T : Sheaf J RingCat.{u + 1}}
    (e : Mon.mk ((sheafCompose J (forget₂ RingCat Ab)).obj S) ≅
      Mon.mk ((sheafCompose J (forget₂ RingCat Ab)).obj T)) : S ≅ T where
  hom := ringSheafMap J e.hom.hom
  inv := ringSheafMap J e.inv.hom
  hom_inv_id := by
    ext U x
    exact congrArg (fun k ↦ k.hom.hom.app U x) e.hom_inv_id
  inv_hom_id := by
    ext U x
    exact congrArg (fun k ↦ k.hom.hom.app U x) e.inv_hom_id

@[irreducible] private def evaluatedRingEquiv
    (R : Type) (S : Type u) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S]
    (q : Profinite.continuousMapRingSheafOfUniverse.{u} R ≅
      Profinite.continuousMapRingSheafOfUniverse.{u} S) : R ≃+* S :=
  (pointEquiv R).trans
    (((((sheafToPresheaf (coherentTopology Profinite.{u}) RingCat).mapIso q).app
      (op (Profinite.of PUnit.{u + 1}))).ringCatIsoToRingEquiv).trans (pointEquiv S).symm)

private theorem idealMapOfMaximal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (g : R ≃+* S) (I : Ideal R) (K : Ideal S)
    (hI : I = IsLocalRing.maximalIdeal R) (hK : K = IsLocalRing.maximalIdeal S) :
    K = I.map g := by
  rw [hI, hK, IsLocalRing.map_ringEquiv_maximalIdeal]

private theorem coefficientSquares
    (R : Type) (S : Type u) [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    [IsLocalRing R] [IsLocalRing S] (I : Ideal R) (K : Ideal S)
    (hI : I = IsLocalRing.maximalIdeal R) (hK : K = IsLocalRing.maximalIdeal S)
    (e : Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheafOfUniverse.{u, 0} R)) ≅
      Mon.mk ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          (Profinite.continuousMapRingSheafOfUniverse.{u, u} S))) :
    ∃ d : Mon.mk (IntegralModelsEmbedded.discreteObj.{u} R) ≅
        Mon.mk (IntegralModelsStacks.discreteObj S),
      ∃ r : Mon.mk (IntegralModelsEmbedded.discreteObj.{u} (R ⧸ I)) ≅
          Mon.mk (IntegralModelsStacks.discreteObj (S ⧸ K)),
        d.hom.hom ≫ (sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsStacks.constantToContinuous S) =
          (sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              (IntegralModelsEmbedded.constantToContinuous R) ≫ e.hom.hom ∧
        d.hom.hom ≫ IntegralModelsStacks.discreteMap (Ideal.Quotient.mk K) =
          IntegralModelsEmbedded.discreteMap (Ideal.Quotient.mk I) ≫ r.hom.hom := by
  let J := coherentTopology Profinite.{u}
  let A := Profinite.continuousMapRingSheafOfUniverse.{u, 0} R
  let B := Profinite.continuousMapRingSheafOfUniverse.{u, u} S
  let q : A ≅ B := ringSheafIso J (S := A) (T := B) e
  let P := Profinite.of PUnit.{u + 1}
  let g : R ≃+* S := evaluatedRingEquiv R S q
  let f : ULift.{u + 1} R ≃+* ULift.{u + 1} S :=
    ULift.ringEquiv.trans (g.trans ULift.ringEquiv.symm)
  let D := constantSheaf J CommRingCat.{u + 1} ⋙
    sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let (X : CommRingCat.{u + 1}) : MonObj (D.obj X) :=
    Sheaf.monObj_sheafCompose_obj J
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf J CommRingCat.{u + 1}).obj X))
  let d₀ := D.mapIso f.toCommRingCatIso
  have : IsMonHom d₀.hom :=
    Sheaf.isMonHom_sheafCompose_map J
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf J CommRingCat.{u + 1}).map f.toCommRingCatIso.hom))
  let d := Mon.mkIso' d₀
  have hd : d.hom.hom ≫ (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsStacks.constantToContinuous S) =
      (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsEmbedded.constantToContinuous.{u} R) ≫ e.hom.hom := by
    let a : (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} R)) ⟶ A.obj :=
      { app U := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := U.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }
    let b : (Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} S)) ⟶ B.obj :=
      { app U := RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ContinuousMap.C (α := U.unop)).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ RingCat.hom_ext (by ext x; rfl) }
    have h : (Functor.const Profinite.{u}ᵒᵖ).map
        ((forget₂ CommRingCat RingCat).map f.toCommRingCatIso.hom) ≫ b =
        a ≫ q.hom.hom := by
      ext U x
      apply ULift.ext
      apply ContinuousMap.ext
      intro y
      let t : U.unop ⟶ P := CompHausLike.ofHom _ (ContinuousMap.const _ PUnit.unit)
      have hn := congrArg (fun k ↦ (k (pointEquiv R x.down)).down y)
        (q.hom.hom.naturality t.op)
      change g x.down = (q.hom.hom.app U (a.app U x)).down y
      unfold g evaluatedRingEquiv
      exact hn.symm
    have hs := constantSquare (CommRingCat.of (ULift.{u + 1} R))
      (CommRingCat.of (ULift.{u + 1} S)) f.toCommRingCatIso.hom q.hom a b h
    have hq : (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map q.hom =
        e.hom.hom := by rfl
    have hh := congrArg ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map) hs
    simp only [Functor.map_comp] at hh
    rw [hq] at hh
    have hdmap : d.hom.hom = D.map f.toCommRingCatIso.hom := rfl
    have ha : (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsEmbedded.constantToContinuous.{u} R) =
        (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (((constantCommuteCompose J
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
              (CommRingCat.of (ULift.{u + 1} R))).hom ≫
            ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _ A).symm a) := by
      rfl
    have hb : (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsStacks.constantToContinuous S) =
        (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (((constantCommuteCompose J
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
              (CommRingCat.of (ULift.{u + 1} S))).hom ≫
            ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _ B).symm b) := by
      rfl
    rw [hdmap, ha, hb]
    simpa only [D, Functor.map_comp, Functor.comp_map, Category.assoc] using hh
  have hIK : K = I.map g := idealMapOfMaximal g I K hI hK
  let r₀ := Ideal.quotientEquiv I K g hIK
  let r' : ULift.{u + 1} (R ⧸ I) ≃+* ULift.{u + 1} (S ⧸ K) :=
    ULift.ringEquiv.trans (r₀.trans ULift.ringEquiv.symm)
  let r₁ := D.mapIso r'.toCommRingCatIso
  have : IsMonHom r₁.hom :=
    Sheaf.isMonHom_sheafCompose_map J
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        ((constantSheaf J CommRingCat.{u + 1}).map r'.toCommRingCatIso.hom))
  refine ⟨d, Mon.mkIso' r₁, hd, ?_⟩
  let i : CommRingCat.of (ULift.{u + 1} R) ⟶ CommRingCat.of (ULift.{u + 1} (R ⧸ I)) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom))
  let k : CommRingCat.of (ULift.{u + 1} S) ⟶ CommRingCat.of (ULift.{u + 1} (S ⧸ K)) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk K).comp ULift.ringEquiv.toRingHom))
  change D.map f.toCommRingCatIso.hom ≫ D.map k = D.map i ≫ D.map r'.toCommRingCatIso.hom
  rw [← D.map_comp, ← D.map_comp]
  apply congrArg D.map
  apply CommRingCat.hom_ext
  ext x
  exact (Ideal.quotientEquiv_mk I K g hIK x.down).symm

/-- An isomorphism of continuous integral coefficients induces commuting isomorphisms
on constant coefficients and their first quotients.

Source: integral-models-stacks, first-quotient transport; Stacks Tag 09C1
(blueprint: lem-sfb-embedded-integral-residue-square).

Proof: evaluate the given monoid-object isomorphism on the one-point profinite set.
Evaluation identifies the continuous functions there with the integer rings and
preserves addition, multiplication and the unit. Naturality for every map from the
point shows that the isomorphism acts on all functions by this ring isomorphism.
In particular it commutes with constant functions. A ring isomorphism of local rings
carries the maximal ideal onto the maximal ideal. The hypothesis identifies the
embedded principal ideal with that maximal ideal; the spectral first coefficient
ideal is also the maximal ideal. The induced quotient ring isomorphism commutes
with the quotient maps. Apply constant sheafification, the forgetful functor to
abelian sheaves and its induced monoid-object functor to both ring isomorphisms.
Functoriality gives the quotient square; the preceding constant-function identity
and the universal property of sheafification give the scalar square. This is an
ordinary coefficient assertion: no scheme, complex, completeness, constructibility
or Tor condition is involved. The identity chart and every automorphism of the
valuation ring give the same construction, including arbitrary uniformizer generators.
-/
theorem embeddedIntegralResidueSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    [FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val)]
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (e : Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.val) ≅
      sfbCondensedIntegers ℓ (ULift.{u} E.val)) :
    ∃ d : Mon.mk (IntegralModelsEmbedded.discreteObj.{u} (PadicAlgCl.integers ℓ E.1)) ≅
        Mon.mk (IntegralModelsStacks.discreteObj
          (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val))),
      ∃ r : Mon.mk (IntegralModelsEmbedded.discreteObj.{u} (completedResidue ℓ E π 0)) ≅
          Mon.mk (IntegralModelsStacks.discreteObj
            (Padic.coefficientExtensionRing ℓ (ULift.{u} E.val) 1)),
        d.hom.hom ≫ IntegralModelsStacks.scalarPointMap ℓ (ULift.{u} E.val) =
          IntegralModelsEmbedded.scalarPointMap ℓ E ≫ e.hom.hom ∧
        d.hom.hom ≫ IntegralModelsStacks.discreteMap
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ (ULift.{u} E.val) 1)) =
          IntegralModelsEmbedded.discreteMap
            (Ideal.Quotient.mk ((Ideal.span {π}) ^ (0 + 1))) ≫ r.hom.hom := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let := spectralNorm.normedField ℚ_[ℓ] (ULift.{u} E.val)
  let mR := (PadicAlgCl.normedFieldOfAlgebra ℓ E.val).toMetricSpace
  let mS := (spectralNorm.normedField ℚ_[ℓ] (ULift.{u} E.val)).toMetricSpace
  let : TopologicalSpace E.val := mR.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : TopologicalSpace (ULift.{u} E.val) :=
    mS.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let R := PadicAlgCl.integers ℓ E.val
  let S := Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.val)
  have hdata := (Padic.coefficientExtensionIntegers_dvr ℓ (ULift.{u} E.val)).choose_spec
  have : IsLocalRing S := hdata.2.2.2.1
  have hmax : Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.val) =
      IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hdata.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer ℓ (ULift.{u} E.val)} =
      Padic.coefficientExtensionMaximalIdeal ℓ (ULift.{u} E.val) :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  let I : Ideal R := Ideal.span {π} ^ (0 + 1)
  let K : Ideal S := Padic.coefficientExtensionIdeal ℓ (ULift.{u} E.val) 1
  have hI : I = IsLocalRing.maximalIdeal R := by
    exact (pow_one _).trans hπ
  have hK : K = IsLocalRing.maximalIdeal S := by
    exact (pow_one _).trans (hgen.trans hmax)
  exact coefficientSquares R S I K hI hK e

end AlgebraicGeometry.ProEtale
