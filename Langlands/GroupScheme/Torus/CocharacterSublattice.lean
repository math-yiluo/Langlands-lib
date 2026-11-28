import Langlands.AbelianScheme.Multiplication
import Langlands.GroupScheme.Absolute.RegularPerturbation
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof
import Langlands.GroupScheme.Torus.SplitCocharacterGeneration
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Isogenies from a finite-index cocharacter sublattice -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]

local notation "B" => Spec (CommRingCat.of F)

open scoped CategoryTheory.MonObj in
/-- A split torus realizing `L`, with the inclusion and multiplication lift on actual
cocharacters, the two composite formulas, and the image on field points. -/
structure CocharacterSublatticeRealization {T : CommGroupScheme B}
    (L : Submodule ℤ (cocharacterLattice T)) (m : ℕ) where
  torus : CommGroupScheme B
  isSplit : IsSplitTorus torus.toGrp
  latticeEquiv : cocharacterLattice torus ≃ₗ[ℤ] L
  hom : torus ⟶ T
  reverse : T ⟶ torus
  hom_cocharacter (ν : cocharacterLattice torus) :
    ν ≫ hom = (latticeEquiv ν : cocharacterLattice T)
  reverse_cocharacter (ν : cocharacterLattice T) :
    (latticeEquiv (ν ≫ reverse) : cocharacterLattice T) = (m : ℤ) • ν
  hom_isIsogeny : IsIsogeny (CommGroupScheme.groupHom hom)
  reverse_isIsogeny : IsIsogeny (CommGroupScheme.groupHom reverse)
  hom_reverse : CommGroupScheme.groupHom hom ≫ CommGroupScheme.groupHom reverse =
    multiplication torus.toGrp (m : ℤ)
  reverse_hom : CommGroupScheme.groupHom reverse ≫ CommGroupScheme.groupHom hom =
    multiplication T.toGrp (m : ℤ)
  range_rationalPoints : (rationalPoints.map (CommGroupScheme.groupHom hom)).range =
    Subgroup.closure {p | ∃ (ℓ : L) (a : Fˣ),
      CocharacterUniformizer.cocharacterPoints F T (ℓ : cocharacterLattice T) a = p}

/-- Realize an integral cocharacter map by summing the coordinate projections followed by
the corresponding images of the coordinate cocharacters. -/
private def homOfCocharacterMap {I : Type u} [Fintype I] {A C : CommGroupScheme B}
    (e : A ≅ splitTorus.commGroupScheme B I)
    (f : cocharacterLattice A →ₗ[ℤ] cocharacterLattice C) : A ⟶ C :=
  e.hom ≫ ∑ i, splitTorus.proj B I i ≫ f (splitTorus.single B I i ≫ e.inv)

private theorem comp_homOfCocharacterMap {I : Type u} [Fintype I] {A C : CommGroupScheme B}
    (e : A ≅ splitTorus.commGroupScheme B I)
    (f : cocharacterLattice A →ₗ[ℤ] cocharacterLattice C) (ν : cocharacterLattice A) :
    ν ≫ homOfCocharacterMap e f = f ν := by
  let c := splitTorus.cocharacterLatticeEquiv F I (ν ≫ e.hom)
  have hν : ∑ i, c i • (splitTorus.single B I i ≫ e.inv) = ν := by
    calc
      _ = (∑ i, c i • splitTorus.single B I i) ≫ e.inv := by
        simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
      _ = (ν ≫ e.hom) ≫ e.inv := by
        rw [← splitTorus.cocharacterLatticeEquiv_symm_eq]
        exact congrArg (fun v => v ≫ e.inv)
          ((splitTorus.cocharacterLatticeEquiv F I).symm_apply_apply (ν ≫ e.hom))
      _ = ν := by simp
  calc
    ν ≫ homOfCocharacterMap e f =
        ∑ i, c i • f (splitTorus.single B I i ≫ e.inv) := by
      rw [homOfCocharacterMap, ← Category.assoc, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (ν ≫ e.hom) ≫ splitTorus.proj B I i = c i • 𝟙 (Gm B) :=
        eq_gmEndEquiv_zsmul F _
      rw [← Category.assoc, hi, Preadditive.zsmul_comp, Category.id_comp]
    _ = f ν := by simp only [← map_smul, ← map_sum, hν]

private theorem hom_ext_of_cocharacters {I : Type u} [Fintype I] {A C : CommGroupScheme B}
    (e : A ≅ splitTorus.commGroupScheme B I) {f g : A ⟶ C}
    (h : ∀ ν : cocharacterLattice A, ν ≫ f = ν ≫ g) : f = g := by
  apply (cancel_epi e.inv).mp
  let d := ∑ i, splitTorus.proj B I i ≫ splitTorus.single B I i
  have hd : d = 𝟙 _ := splitTorus.sum_proj_comp_single B I
  calc
    e.inv ≫ f = d ≫ (e.inv ≫ f) := by rw [hd, Category.id_comp]
    _ = d ≫ (e.inv ≫ g) := by
      simp only [d, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa only [Category.assoc] using
        congrArg (fun v : cocharacterLattice C => splitTorus.proj B I i ≫ v)
          (h (splitTorus.single B I i ≫ e.inv))
    _ = e.inv ≫ g := by rw [hd, Category.id_comp]

private theorem injective_character_pullback {A C : CommGroupScheme B}
    (hC : IsSplitTorus C.toGrp) (f : A ⟶ C) (g : C ⟶ A) {n : ℤ} (hn : n ≠ 0)
    (h : g ≫ f = n • 𝟙 C) : Function.Injective (fun χ : characterLattice C => f ≫ χ) := by
  intro χ ψ hχψ
  have hscaled : n • χ = n • ψ := by
    have he := congrArg (fun ξ : characterLattice A => g ≫ ξ) hχψ
    change g ≫ (f ≫ χ) = g ≫ (f ≫ ψ) at he
    simpa only [← Category.assoc, h, Preadditive.zsmul_comp, Category.id_comp] using he
  apply hC.isPerfPair_latticePairing.bijective_left.injective
  apply LinearMap.ext
  intro ν
  apply smul_right_injective ℤ hn
  simpa only [map_smul, LinearMap.smul_apply] using
    congrArg (fun ξ : characterLattice C => latticePairing C ξ ν) hscaled

open scoped CategoryTheory.MonObj in
private theorem range_rationalPoints_of_cocharacterEquiv {A T : CommGroupScheme B}
    (hA : IsSplitTorus A.toGrp) {L : Submodule ℤ (cocharacterLattice T)}
    (e : cocharacterLattice A ≃ₗ[ℤ] L) (h : A ⟶ T)
    (hh : ∀ ν : cocharacterLattice A, ν ≫ h = (e ν : cocharacterLattice T)) :
    (rationalPoints.map (CommGroupScheme.groupHom h)).range =
      Subgroup.closure {p | ∃ (ℓ : L) (a : Fˣ),
        CocharacterUniformizer.cocharacterPoints F T (ℓ : cocharacterLattice T) a = p} := by
  let hF := rationalPoints.map (CommGroupScheme.groupHom h)
  have heval (c : cocharacterLattice A) (a : Fˣ) :
      hF (CocharacterUniformizer.cocharacterPoints F A c a) =
        CocharacterUniformizer.cocharacterPoints F T (e c : cocharacterLattice T) a := by
    rw [← hh c]
    simp only [hF, CocharacterUniformizer.cocharacterPoints, MonoidHom.comp_apply,
      rationalPoints.map_apply, comp_groupHom_comp]
  change hF.range = _
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    obtain ⟨I, hI, ν, hprod⟩ := hA.exists_cocharacterPoints_prod
    let : Fintype I := hI
    obtain ⟨a, ha⟩ := hprod q
    rw [ha, map_prod]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [heval]
    exact Subgroup.subset_closure ⟨e (ν i), a i, rfl⟩
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨ℓ, a, rfl⟩
    refine ⟨CocharacterUniformizer.cocharacterPoints F A (e.symm ℓ) a, ?_⟩
    change hF (CocharacterUniformizer.cocharacterPoints F A (e.symm ℓ) a) = _
    rw [heval, e.apply_symm_apply]

/-- Realize a submodule containing `m` times the actual integral cocharacter lattice of a
split torus by two isogenies whose composites are multiplication by `m`. -/
def IsSplitTorus.realizeCocharacterSublattice {T : CommGroupScheme B}
    (hT : IsSplitTorus T.toGrp) (L : Submodule ℤ (cocharacterLattice T))
    (m : ℕ) (hm : 0 < m) (hL : ∀ ν : cocharacterLattice T, (m : ℤ) • ν ∈ L) :
    CocharacterSublatticeRealization L m := by
  let I := hT.choose
  letI : Finite I := hT.choose_spec.choose
  letI : Fintype I := Fintype.ofFinite I
  let eT : T ≅ splitTorus.commGroupScheme B I :=
    CommGroupScheme.isoOfGroupIso hT.choose_spec.choose_spec.some
  let cT : cocharacterLattice T ≃ₗ[ℤ] (I → ℤ) := ((cocharacterLattice.congr eT).trans
    (splitTorus.cocharacterLatticeEquiv F I)).toIntLinearEquiv
  let b := Submodule.basisOfPid ((Pi.basisFun ℤ I).map cT.symm) L
  let J := ULift.{u} (Fin b.1)
  let bL : Module.Basis J ℤ L := b.2.reindex Equiv.ulift.symm
  let S := splitTorus.commGroupScheme B J
  let hS : IsSplitTorus S.toGrp := isSplitTorus_splitTorus J
  let eL : cocharacterLattice S ≃ₗ[ℤ] L :=
    (splitTorus.cocharacterLatticeEquiv F J).toIntLinearEquiv.trans bL.equivFun.symm
  let hY := L.subtype.comp eL.toLinearMap
  let mY := ((m : ℤ) • (LinearMap.id :
    cocharacterLattice T →ₗ[ℤ] cocharacterLattice T)).codRestrict L hL
  let gY := eL.symm.toLinearMap.comp mY
  let h : S ⟶ T := homOfCocharacterMap (Iso.refl S) hY
  let g : T ⟶ S := homOfCocharacterMap eT gY
  have hh (ν : cocharacterLattice S) : ν ≫ h = (eL ν : cocharacterLattice T) :=
    comp_homOfCocharacterMap (Iso.refl S) hY ν
  have hg (ν : cocharacterLattice T) : (eL (ν ≫ g) : cocharacterLattice T) = (m : ℤ) • ν := by
    rw [show ν ≫ g = eL.symm (mY ν) from comp_homOfCocharacterMap eT gY ν,
      eL.apply_symm_apply]
    rfl
  have hcompT : g ≫ h = (m : ℤ) • 𝟙 T := by
    apply hom_ext_of_cocharacters eT
    intro ν
    rw [← Category.assoc, hh, hg, Preadditive.comp_zsmul, Category.comp_id]
  have hcompS : h ≫ g = (m : ℤ) • 𝟙 S := by
    apply hom_ext_of_cocharacters (Iso.refl S)
    intro ν
    rw [← Category.assoc, Preadditive.comp_zsmul, Category.comp_id]
    apply eL.injective
    apply Subtype.ext
    rw [hg, map_smul, hh]
    rfl
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hm.ne'
  have hhinj : Function.Injective (fun ν : cocharacterLattice S => ν ≫ h) := by
    intro ν μ hνμ
    change ν ≫ h = μ ≫ h at hνμ
    rw [hh, hh] at hνμ
    exact eL.injective (Subtype.ext hνμ)
  have hginj : Function.Injective (fun ν : cocharacterLattice T => ν ≫ g) := by
    let := hT.torsionFree_cocharacterLattice
    intro ν μ hνμ
    change ν ≫ g = μ ≫ g at hνμ
    apply smul_right_injective (cocharacterLattice T) hm'
    change (m : ℤ) • ν = (m : ℤ) • μ
    rw [← hg ν, ← hg μ, hνμ]
  exact
    { torus := S
      isSplit := hS
      latticeEquiv := eL
      hom := h
      reverse := g
      hom_cocharacter := hh
      reverse_cocharacter := hg
      hom_isIsogeny := splitTorusIsogenyOfLatticeMaps F S T h hS hT
        (injective_character_pullback hT h g hm' hcompT) hhinj
      reverse_isIsogeny := splitTorusIsogenyOfLatticeMaps F T S g hT hS
        (injective_character_pullback hS g h hm' hcompS) hginj
      hom_reverse := congrArg CommGroupScheme.groupHom hcompS
      reverse_hom := congrArg CommGroupScheme.groupHom hcompT
      range_rationalPoints := range_rationalPoints_of_cocharacterEquiv hS eL h hh }

end Langlands.GroupScheme
