import Langlands.GroupScheme.Torus.EndomorphismDichotomyStatement
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCharacters
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.LinearAlgebra.FreeModule.PID

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusEndomorphism

/-- A noninjective endomorphism of a finite free integer lattice has a
primitive functional annihilating its image. -/
theorem exists_surjective_annihilator
    {I : Type u} [Finite I] (f : (I → ℤ) →ₗ[ℤ] (I → ℤ))
    (hf : ¬ Function.Injective f) :
    ∃ q : (I → ℤ) →ₗ[ℤ] ℤ, Function.Surjective q ∧ ∀ x, q (f x) = 0 := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨n, s⟩ := (LinearMap.range f).smithNormalForm (Pi.basisFun ℤ I)
  have hs : ¬ Function.Surjective s.f := by
    intro h
    let e : Fin n ≃ I := Equiv.ofBijective s.f ⟨s.f.injective, h⟩
    let l : (I → ℤ) ≃ₗ[ℤ] LinearMap.range f :=
      s.bM.equiv s.bN e.symm
    have hsurj : Function.Surjective f.rangeRestrict := by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
    have hinj : Function.Injective f.rangeRestrict :=
      (OrzechProperty.bijective_of_surjective_of_injective l.toLinearMap
        f.rangeRestrict l.injective hsurj).1
    apply hf
    intro x y hxy
    exact hinj (Subtype.ext hxy)
  obtain ⟨i, hi⟩ : ∃ i, i ∉ Set.range s.f := by
    simpa only [Function.Surjective, Set.mem_range, not_forall] using hs
  refine ⟨s.bM.coord i, ?_, ?_⟩
  · intro z
    refine ⟨z • s.bM i, ?_⟩
    change (s.bM.repr (z • s.bM i)) i = z
    rw [map_smul, Module.Basis.repr_self]
    simp
  · intro x
    exact s.le_ker_coord_of_notMem_range hi (LinearMap.mem_range_self f x)

end TorusEndomorphism

namespace Diagonalizable

/-- Surjective exponent maps induce closed immersions of diagonalizable groups. -/
theorem isClosedImmersion_restrictMap
    (R : CommRingCat.{u}) {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    (g : M →+ N) (hg : Function.Surjective g) :
    IsClosedImmersion (restrictMap R g).hom.hom.left := by
  rw [restrictMap_left, ← incl_toRingHom]
  exact IsClosedImmersion.spec_of_surjective _ (incl_surjective g hg)

/-- A zero composite of exponent maps gives the zero composite on actual groups. -/
theorem restrictMap_comp_eq_zero
    (R : CommRingCat.{u}) {L M N : Type u}
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    (g : M →+ N) (h : L →+ M) (hzero : ∀ l, g (h l) = 0) :
    (Additive.ofMul (restrictMap R g) :
        groupScheme R N ⟶ groupScheme R M) ≫
      Additive.ofMul (restrictMap R h) = 0 := by
  apply CommGroupScheme.hom_ext_points
  intro T x
  change x ≫ ((restrictMap R g).hom.hom ≫ (restrictMap R h).hom.hom) =
    x ≫ (CommGroupScheme.groupHom
      (0 : groupScheme R N ⟶ groupScheme R L)).hom.hom
  rw [← Category.assoc, comp_groupHom_zero]
  apply (Corepresented.pointsEquiv (functor R L) (grpCorepresentation R L) T).injective
  apply MonoidHom.ext
  intro l
  change
    DFunLike.coe (F := Multiplicative L →* ((algΓ R).obj T).unopˣ)
      (Corepresented.pointsEquiv (functor R L) (grpCorepresentation R L) T
      ((x ≫ (restrictMap R g).hom.hom) ≫ (restrictMap R h).hom.hom))
        (Multiplicative.ofAdd l.toAdd) = _
  rw [pointsEquiv_restrictMap, pointsEquiv_restrictMap, hzero, map_one]
  exact map_one (F := Multiplicative N →* ((algΓ R).obj T).unopˣ)
    (Corepresented.pointsEquiv (functor R N) (grpCorepresentation R N) T x)

end Diagonalizable

namespace TorusEndomorphism

/-- The dichotomy for the standard split torus, via its actual character map. -/
theorem split_surjective_or_closedGm
    {k : Type u} [Field k] (I : Type u) [Finite I]
    (f : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) I) :
    Surjective f.hom.hom.left ∨
      ∃ ν : Gm (Spec (CommRingCat.of k)) ⟶
          splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I,
        IsClosedSubgroup (CommGroupScheme.groupHom ν) ∧
          ν ≫ (Additive.ofMul f :
            splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶
              splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) = 0 := by
  classical
  let := Fintype.ofFinite I
  let R := CommRingCat.of k
  let S := Spec R
  let h := splitTorus.characterMap I I f
  let E := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))
  have hE : Diagonalizable.restrictMap R h.toAddMonoidHom ≫ E.hom = E.hom ≫ f :=
    splitTorus.diagonalizableMap_splitIso I I f
  have : IsIso E.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E.hom
  have : IsIso E.inv.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E.inv
  by_cases hh : Function.Injective h
  · left
    have hs := (Diagonalizable.flat_and_surjective_restrictMap R
      h.toAddMonoidHom hh).2
    have he : f = E.inv ≫ Diagonalizable.restrictMap R h.toAddMonoidHom ≫ E.hom := by
      calc
        f = (E.inv ≫ E.hom) ≫ f := by simp
        _ = E.inv ≫ Diagonalizable.restrictMap R h.toAddMonoidHom ≫ E.hom := by
          rw [Category.assoc, ← hE]
    rw [he]
    change Surjective (E.inv.hom.hom.left ≫
      (Diagonalizable.restrictMap R h.toAddMonoidHom).hom.hom.left ≫ E.hom.hom.hom.left)
    infer_instance
  · right
    obtain ⟨q, hq, hzero⟩ := exists_surjective_annihilator h hh
    let g : (I → ℤ) →+ (PUnit.{u+1} → ℤ) :=
      { toFun := fun m _ => q m
        map_zero' := by funext i; exact q.map_zero
        map_add' := by intro m n; funext i; exact q.map_add m n }
    have hg : Function.Surjective g := by
      intro y
      obtain ⟨x, hx⟩ := hq (y PUnit.unit)
      refine ⟨x, ?_⟩
      funext i
      change q x = y i
      simpa only [Subsingleton.elim i PUnit.unit] using hx
    let E1 : (Gm S).toGrp ≅ (Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ)).toGrp :=
      splitTorus.gmIso S ≪≫
        (Diagonalizable.splitIso R (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
    let C1 : Gm S ≅ Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ) :=
      CommGroupScheme.isoOfGroupIso E1
    let C : Diagonalizable.groupScheme R (I → ℤ) ≅ splitTorus.commGroupScheme S I :=
      CommGroupScheme.isoOfGroupIso E
    let δ : Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ) ⟶
        Diagonalizable.groupScheme R (I → ℤ) := Additive.ofMul (Diagonalizable.restrictMap R g)
    let φ : Diagonalizable.groupScheme R (I → ℤ) ⟶
        Diagonalizable.groupScheme R (I → ℤ) :=
      Additive.ofMul (Diagonalizable.restrictMap R h.toAddMonoidHom)
    let fC : splitTorus.commGroupScheme S I ⟶ splitTorus.commGroupScheme S I :=
      Additive.ofMul f
    have hC : φ ≫ C.hom = C.hom ≫ fC :=
      congrArg Additive.ofMul hE
    have hz : δ ≫ φ = 0 :=
      Diagonalizable.restrictMap_comp_eq_zero R g h.toAddMonoidHom
        (fun x => funext fun _ => hzero x)
    let ν : Gm S ⟶ splitTorus.commGroupScheme S I := C1.hom ≫ δ ≫ C.hom
    refine ⟨ν, ?_, ?_⟩
    · have : IsIso E1.hom.hom.hom.left :=
        Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E1.hom
      have := Diagonalizable.isClosedImmersion_restrictMap R g hg
      change IsClosedImmersion (E1.hom.hom.hom.left ≫
        (Diagonalizable.restrictMap R g).hom.hom.left ≫ E.hom.hom.hom.left)
      infer_instance
    · calc
        ν ≫ fC = C1.hom ≫ (δ ≫ φ) ≫ C.hom := by
          dsimp only [ν]
          simp only [Category.assoc, hC]
        _ = 0 := by rw [hz]; simp

end TorusEndomorphism

/-- Every torus endomorphism over an algebraically closed field is scheme
surjective or kills an actual closed multiplicative subgroup. -/
theorem torusEndomorphismDichotomy : TorusEndomorphismDichotomyStatement.{u} := by
  intro k _ _ T hT f
  classical
  have hsplit : IsSplitTorus T.toGrp :=
    SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
      Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T.toGrp hT
  obtain ⟨I, hI, ⟨e⟩⟩ := hsplit
  let C : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let g : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶
      splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I := C.inv ≫ f ≫ C.hom
  have : IsIso e.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) e.hom
  have : IsIso e.inv.hom.hom.left :=
    Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) e.inv
  rcases TorusEndomorphism.split_surjective_or_closedGm I
    (CommGroupScheme.groupHom g) with hg | ⟨ν, hν, hzero⟩
  · left
    have hf : f = C.hom ≫ g ≫ C.inv := by
      dsimp only [g]
      simp
    have hleft := congrArg
      (fun z : T ⟶ T => (CommGroupScheme.groupHom z).hom.hom.left) hf
    rw [hleft]
    change Surjective (e.hom.hom.hom.left ≫
      (CommGroupScheme.groupHom g).hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  · right
    refine ⟨ν ≫ C.inv, ?_, ?_⟩
    · have : IsClosedImmersion (CommGroupScheme.groupHom ν).hom.hom.left := hν
      change IsClosedImmersion
        ((CommGroupScheme.groupHom ν).hom.hom.left ≫ e.inv.hom.hom.left)
      infer_instance
    · change ν ≫ g = 0 at hzero
      have hf : C.inv ≫ f = g ≫ C.inv := by
        dsimp only [g]
        simp
      calc
        (ν ≫ C.inv) ≫ f = (ν ≫ g) ≫ C.inv := by
          simp only [Category.assoc, hf]
        _ = 0 := by rw [hzero]; simp

/-- Choose the actual closed multiplicative subgroup killed by a nonsurjective
torus endomorphism. -/
def TorusEndomorphism.kernelGm
    {k : Type u} [Field k] [IsAlgClosed k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp)
    (f : T ⟶ T) (hf : ¬ Surjective (CommGroupScheme.groupHom f).hom.hom.left) :
    {ν : Gm (Spec (CommRingCat.of k)) ⟶ T //
      IsClosedSubgroup (CommGroupScheme.groupHom ν) ∧ ν ≫ f = 0} :=
  Classical.choice (by
    rcases torusEndomorphismDichotomy k T hT f with h | ⟨ν, hν, hzero⟩
    · exact (hf h).elim
    · exact ⟨⟨ν, hν, hzero⟩⟩)

end Langlands.GroupScheme
