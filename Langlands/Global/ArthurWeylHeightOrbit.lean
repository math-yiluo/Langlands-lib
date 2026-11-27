import Langlands.Global.ArthurWeylHeightCharacters
import Langlands.Global.ArthurTruncationEigenlineHeight
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.MinimalParabolicLineCharacter

/-! # Comparing Iwasawa logarithms on Weyl-translated unipotent orbits -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily Langlands.Automorphic.GroupSchemeFunctions
  AdelicGroupPoints ArthurParabolicSpaces RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)

local notation "A" => AdelicGroupPoints F G
local notation "P₀" => Standard.parabolicScheme i ν ∅
local notation "L₀" => Standard.leviScheme i ν ∅
local notation "U₀" => Standard.unipotentScheme i ν ∅
local notation "p₀" => Standard.parabolicHom i ν ∅
local notation "l₀" => Standard.leviToParabolic i ν ∅
local notation "u₀" => Standard.unipotentToParabolic i ν ∅
local notation "j₀" => torusToParabolic F i ν ∅
local notation "N₀" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν ∅))
local notation "A₀" => CommAlgCat.of F (Adeles F)
local notation "aPoint" => innerAdelicPoint F G

private theorem character_comp_eval {E P : GroupScheme (Spec (CommRingCat.of F))}
    (f : E ⟶ P) (χ : rationalCharacters P) (m : AdelicGroupPoints F E) :
    character F P χ.toMul (map F E P f m) = character F E (characterRestrict f χ).toMul m := by
  change Gm.affineUnitsEquiv _ _ ((m ≫ f.hom.hom) ≫ χ.toMul.hom.hom) = _
  rw [Category.assoc]
  rfl

include hG hi hν in
omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem exists_weyl_levi_factor (n : normalizerPoints i) :
    ∃ b : L₀ ⟶ P₀, b ≫ p₀ = Standard.leviHom i ν ∅ ≫ (G.innerIso (n⁻¹ : normalizerPoints i).val).hom ∧
      standardLeviTorusFactor i ν ∅ (Standard.isRepresentedBy_leviHom i ν ∅) ≫ b =
        CommGroupScheme.groupHom (normalizingAut i n).inv ≫ j₀ := by
  let l := Standard.leviHom i ν ∅
  let c := (G.innerIso (n⁻¹ : normalizerPoints i).val).hom
  have hL := standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν
  have hRange : SubgroupFunctor.range (l ≫ c) ≤ standardParabolic i ν ∅ := by
    intro X y hy
    obtain ⟨m, rfl⟩ := hy
    let m' : X ⟶ (L₀).X := m
    apply standardLevi_le_standardParabolic i ν ∅ X
    rw [hL]
    have hm := (Standard.isRepresentedBy_leviHom i ν ∅).pointsEquiv X m |>.property
    change m' ≫ l.hom.hom ∈ (standardLevi i ν ∅).carrier X at hm
    rw [hL] at hm
    have he := torusCentralizer_comap_innerIso_normalizer i n⁻¹
    have hm' : m' ≫ l.hom.hom ∈ ((torusCentralizer i).comap c).carrier X := he.symm ▸ hm
    rw [SubgroupFunctor.mem_comap] at hm'
    change m' ≫ (l ≫ c).hom.hom ∈ (torusCentralizer i).carrier X
    rwa [Grp.comp_hom_hom, ← Category.assoc]
  let hp := Standard.isRepresentedBy_parabolicHom i ν ∅
  let b := hp.factorHom (l ≫ c) hRange
  have hb := hp.factorHom_comp (l ≫ c) hRange
  refine ⟨b, hb, hp.hom_ext ?_⟩
  rw [Category.assoc, hb, ← Category.assoc, standardLeviTorusFactor_comp, Category.assoc,
    torusToParabolic_comp]
  exact (isNormalizingPoint_normalizingAut i n).inv

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
private theorem adelicMatrix_map_comp {P : GroupScheme (Spec (CommRingCat.of F))} {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (p : P ⟶ G) (q : AdelicGroupPoints F P) :
    adelicMatrix F G ρ (map F P G p q) = (ρ.restrict p).affineMatrix A₀ q := by
  change ρ.affineMatrix A₀ (q ≫ p.hom.hom) = _
  rw [MatrixRepresentation.affineMatrix_restrict]

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem eigenvector_adelicMatrix_of_line {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (j : Fin d) (hline : (ρ.restrict p₀).PreservesCoordinateLine j)
    (q : AdelicGroupPoints F P₀) :
    (adelicMatrix F G ρ (map F P₀ G p₀ q)).val *ᵥ (Pi.single j 1 : Fin d → Adeles F) =
      (character F P₀ ((ρ.restrict p₀).coordinateLineRationalCharacter j hline).toMul q).val •
        (Pi.single j 1 : Fin d → Adeles F) := by
  rw [adelicMatrix_map_comp]
  exact (ρ.restrict p₀).affine_coordinateLineCharacter_action j hline A₀ q

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem adelicMatrix_Levi_column_eq {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (j : Fin d) (hline : (ρ.restrict p₀).PreservesCoordinateLine j)
    (n : normalizerPoints i) (b : L₀ ⟶ P₀)
    (hb : b ≫ p₀ = Standard.leviHom i ν ∅ ≫ (G.innerIso (n⁻¹ : normalizerPoints i).val).hom)
    (m : AdelicGroupPoints F L₀) :
    let e := (Pi.single j 1 : Fin d → Adeles F)
    let M := adelicMatrix F G ρ (aPoint n.val)
    (adelicMatrix F G ρ (map F L₀ G (Standard.leviHom i ν ∅) m)).val *ᵥ (M.val *ᵥ e) =
      (character F P₀ ((ρ.restrict p₀).coordinateLineRationalCharacter j hline).toMul
        (map F L₀ P₀ b m)).val • (M.val *ᵥ e) := by
  intro e M
  let a := aPoint n.val
  let z := map F L₀ G (Standard.leviHom i ν ∅) m
  have hInv : aPoint (n⁻¹ : normalizerPoints i).val = a⁻¹ := by
    simp only [← principalPoint_eq_innerAdelicPoint, Subgroup.coe_inv, map_inv, a]
  have hmap : map F P₀ G p₀ (map F L₀ P₀ b m) = a⁻¹ * z * a := by
    rw [← map_comp_apply_of_hom, hb, map_comp_apply_of_hom]
    change G.affinePointsTarget (G.innerIso (n⁻¹ : normalizerPoints i).val).hom A₀ z = _
    rw [affinePointsTarget_innerIso_hom, hInv, inv_inv]
  have he := eigenvector_adelicMatrix_of_line ρ j hline (map F L₀ P₀ b m)
  rw [hmap] at he
  have hz : z * a = a * (a⁻¹ * z * a) := by group
  change (adelicMatrix F G ρ z).val *ᵥ ((adelicMatrix F G ρ a).val *ᵥ e) = _
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, hz, map_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, show e = (Pi.single j 1 : Fin d → Adeles F) from rfl, he,
    Matrix.mulVec_smul]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
private theorem adelicMatrix_innerAdelicPoint_column {d : ℕ}
    (ρ : MatrixRepresentation G (Fin d)) (n : normalizerPoints i) (j : Fin d) :
    (adelicMatrix F G ρ (aPoint n.val)).val *ᵥ (Pi.single j 1 : Fin d → Adeles F) =
      PrimitiveAdelicHeight.rational F d ((ρ.rationalMatrix n.val).val *ᵥ Pi.single j 1) := by
  have h := ρ.affineMatrix_constantPoint n.val A₀
  change adelicMatrix F G ρ (aPoint n.val) = _ at h
  rw [h]
  ext b
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.GeneralLinearGroup.map_apply,
    PrimitiveAdelicHeight.rational]

include hG hi in
omit [Mono i.hom.hom.left] [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 800000 in
private theorem adelicMatrix_unipotent_column_sameWeight {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (e : Fin d → ℤ) (he : (CommGroupScheme.groupHom ν ≫ i) ≫ ρ =
      GeneralLinear.diagonalCocharacter (Fin d) (CommRingCat.of F) e)
    (v : Fin d → F) (a : Fin d) (hv : ∀ b, e b ≠ e a → v b = 0) (u : AdelicGroupPoints F U₀) :
    ((adelicMatrix F G ρ (map F U₀ G (Standard.unipotentHom i ν ∅) u)).val *ᵥ
      PrimitiveAdelicHeight.rational F d v) a = algebraMap F (Adeles F) (v a) := by
  classical
  let X₀ := (algSpec (CommRingCat.of F)).obj (op A₀)
  let c := CommGroupScheme.groupHom ν ≫ i
  let uG := map F U₀ G (Standard.unipotentHom i ν ∅) u
  have hu : uG ∈ (Dynamic.unipotent c).carrier X₀ := by
    rw [← standardUnipotent_empty_eq_dynamic i ν hG hi]
    exact (Standard.isRepresentedBy_unipotentHom i ν ∅).pointsEquiv X₀ u |>.property
  have hmat := Dynamic.unipotent_le_comap c ρ X₀ hu
  rw [SubgroupFunctor.mem_comap, he, GeneralLinear.unipotent_diagonalCocharacter,
    GeneralLinear.mem_blockUnipotent] at hmat
  have hentry (b : Fin d) (hb : e a ≤ e b) :
      (adelicMatrix F G ρ uG).val a b = (1 : Matrix (Fin d) (Fin d) (Adeles F)) a b := by
    have h := hmat a b hb
    change (ρ.pointMatrix X₀ uG).val a b = _ at h
    let E := Corepresented.affineSectionsAlgEquiv (R := CommRingCat.of F) A₀
    have he' : (ρ.pointMatrix X₀ uG).val a b = E.symm ((ρ.affineMatrix A₀ uG).val a b) := by
      rw [ρ.pointMatrix_eq_affineMatrix A₀]
      rfl
    rw [he'] at h
    have hh := congrArg E h
    rw [E.apply_symm_apply] at hh
    change (ρ.affineMatrix A₀ uG).val a b = _
    by_cases hab : a = b
    · subst b
      rw [Matrix.one_apply_eq] at hh ⊢
      exact hh.trans (map_one E)
    · rw [Matrix.one_apply_ne hab] at hh ⊢
      exact hh.trans (map_zero E)
  change (∑ b, (adelicMatrix F G ρ uG).val a b * algebraMap F (Adeles F) (v b)) = _
  rw [Finset.sum_eq_single a]
  · rw [hentry a le_rfl, Matrix.one_apply_eq, one_mul]
  · intro b _ hb
    by_cases heq : e b = e a
    · rw [hentry b heq.ge, Matrix.one_apply_ne (Ne.symm hb), zero_mul]
    · rw [hv b heq, map_zero, mul_zero]
  · simp

include hG hi hν in
omit [LocallyOfFiniteType G.X.hom] in
set_option maxHeartbeats 1500000 in
/-- On a Weyl-translated orbit, the minimal-parabolic line character admits the
uniform lower bound in its Weyl translate. -/
theorem exists_weylLineHeight_bound {d : ℕ} (ρ : MatrixRepresentation G (Fin d))
    (j : Fin d) (hP : (ρ.restrict p₀).PreservesCoordinateLine j)
    (n : normalizerPoints i) :
    ∃ (χ₂ : rationalCharacters P₀) (B : ℝ), 0 ≤ B ∧
      torusCharacterRestrict j₀ χ₂ = weylAction i n
        (torusCharacterRestrict j₀ ((ρ.restrict p₀).coordinateLineRationalCharacter j hP)) ∧
      ∀ (v : N₀) (x : A),
        hK.height x ((ρ.restrict p₀).coordinateLineRationalCharacter j hP) ≤
          hK.height (aPoint n.val * (v : A) * x) χ₂ + B := by
  classical
  let χ₁ := (ρ.restrict p₀).coordinateLineRationalCharacter j hP
  let c := CommGroupScheme.groupHom ν ≫ i
  have hP' : (Dynamic.parabolic c).IsRepresentedBy p₀ := by
    rw [← standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
    exact Standard.isRepresentedBy_parabolicHom i ν ∅
  have hline := ρ.preservesCoordinateLine_cocharacter_of_parabolic c p₀ hP' j hP
  obtain ⟨B, e, a, hB, -, he⟩ := (ρ.restrict c).exists_diagonalization_retaining_coordinateLine j hline
  let σ := ρ.basisConjugate B
  have heq : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin d) (CommRingCat.of F) e := by
    rw [← he]
    exact (Category.assoc _ _ _).symm
  have hσP : (σ.restrict p₀).PreservesCoordinateLine a := by
    intro X x
    obtain ⟨s, hs⟩ := hP X x
    refine ⟨s, ?_⟩
    rw [MatrixRepresentation.pointMatrix_restrict] at hs ⊢
    exact (ρ.basisConjugate_coordinateScalar_iff B a j hB X (x ≫ (p₀).hom.hom) s.val).mpr hs
  have hχ : (σ.restrict p₀).coordinateLineRationalCharacter a hσP = χ₁ := by
    apply Additive.toMul.injective
    change (σ.restrict p₀).coordinateLineCharacter a hσP = (ρ.restrict p₀).coordinateLineCharacter j hP
    exact (ρ.restrict p₀).basisConjugate_coordinateLineCharacter B a j hB hP hσP
  let c' := CommGroupScheme.groupHom (GroupScheme.cocharacterAut (normalizingAut i n⁻¹) ν) ≫ i
  have hc' : c' ≫ (G.innerIso n.val).hom = c := by
    dsimp only [c']
    rw [groupHom_cocharacterAut_comp, Category.assoc, Subgroup.coe_inv, innerIso_inv_hom,
      Iso.inv_hom_id, Category.comp_id]
  have hσT := σ.preservesCoordinateLine_torus_of_minimalStandardParabolic i hG hi ν hν a hσP
  have hσc' : (σ.restrict c').PreservesCoordinateLine a :=
    MatrixRepresentation.preservesCoordinateLine_restrict_comp σ i _ a hσT
  let t := (σ.restrict c').coordinateLineCocharacterWeight a hσc'
  have ht := (σ.restrict c').hasCoordinatePowerAction_coordinateLineCocharacterWeight a hσc'
  let v₁ : Fin d → F := Pi.single a 1
  let v₂ := (σ.rationalMatrix n.val).val *ᵥ v₁
  have hv₁ : v₁ ≠ 0 := by
    intro hz
    have h := congrFun hz a
    simp [v₁] at h
  have hv₂ : v₂ ≠ 0 := by
    intro hz
    apply hv₁
    apply Matrix.mulVec_injective_of_isUnit (Units.isUnit (σ.rationalMatrix n.val))
    simpa only [Matrix.mulVec_zero] using hz
  obtain ⟨j', hj'⟩ : ∃ j' : Fin d, v₂ j' ≠ 0 := by
    by_contra! h
    exact hv₂ (funext h)
  have hv₂supp (b : Fin d) (hb : e b ≠ t) : v₂ b = 0 := by
    change ((σ.rationalMatrix n.val).val *ᵥ Pi.single a 1) b = 0
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
    exact σ.rationalMatrix_entry_eq_zero_of_conj_powerAction c c' e heq hc' a t ht hb
  have hej : e j' = t := not_ne_iff.mp (fun hn => hj' (hv₂supp j' hn))
  have hv₂supp' (b : Fin d) (hb : e b ≠ e j') : v₂ b = 0 := hv₂supp b (hej ▸ hb)
  have hS := Standard.parabolicStructure i ν hG hi hν ∅ (Set.empty_subset _)
  let : IsIso (subgroupMultiplication l₀ u₀) := hS.2.2.2
  let L := leviRetraction l₀ u₀ hS.2.2.1.1.isNormal
  obtain ⟨b, hb, hbt⟩ := exists_weyl_levi_factor hG hi hν n
  let χ₂ := characterRestrict (L ≫ b) χ₁
  have hjL : j₀ = standardLeviTorusFactor i ν ∅ (Standard.isRepresentedBy_leviHom i ν ∅) ≫ l₀ := by
    apply (Standard.isRepresentedBy_parabolicHom i ν ∅).hom_ext
    rw [torusToParabolic_comp, Category.assoc, Standard.leviToParabolic_comp,
      standardLeviTorusFactor_comp]
  have hret : j₀ ≫ L ≫ b = CommGroupScheme.groupHom (normalizingAut i n).inv ≫ j₀ := by
    have hL : l₀ ≫ L = 𝟙 L₀ := levi_comp_leviRetraction l₀ u₀ hS.2.2.1.1.isNormal
    calc
      j₀ ≫ L ≫ b = (standardLeviTorusFactor i ν ∅ (Standard.isRepresentedBy_leviHom i ν ∅)
          ≫ (l₀ ≫ L)) ≫ b := by rw [hjL]; simp only [Category.assoc]
      _ = _ := by rw [hL, Category.comp_id, hbt]
  have hχ₂ : torusCharacterRestrict j₀ χ₂ = weylAction i n (torusCharacterRestrict j₀ χ₁) := by
    rw [weylAction_apply]
    change Additive.ofMul (j₀ ≫ (L ≫ b) ≫ χ₁.toMul) =
      Additive.ofMul (CommGroupScheme.groupHom (normalizingAut i n).inv ≫ j₀ ≫ χ₁.toMul)
    congr 1
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f : T.toGrp ⟶ P₀ => f ≫ χ₁.toMul) hret).trans (Category.assoc _ _ _))
  have hv₁A : PrimitiveAdelicHeight.rational F d v₁ = (Pi.single a 1 : Fin d → Adeles F) := by
    ext b
    by_cases hb' : b = a <;> simp [v₁, PrimitiveAdelicHeight.rational, hb']
  have h1 (q : AdelicGroupPoints F P₀) :
      (adelicMatrix F G σ (map F P₀ G p₀ q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₁ =
        (character F P₀ χ₁.toMul q).val • PrimitiveAdelicHeight.rational F d v₁ := by
    rw [hv₁A, ← hχ]
    exact eigenvector_adelicMatrix_of_line σ a hσP q
  have hv₂A := adelicMatrix_innerAdelicPoint_column σ n a
  have h2 (q : AdelicGroupPoints F P₀) :
      ((adelicMatrix F G σ (map F P₀ G p₀ q)).val *ᵥ PrimitiveAdelicHeight.rational F d v₂) j' =
        (character F P₀ χ₂.toMul q).val * algebraMap F (Adeles F) (v₂ j') := by
    let m : AdelicGroupPoints F L₀ := (leviComponent l₀ u₀ q⁻¹)⁻¹
    let u : AdelicGroupPoints F U₀ := (radicalComponent l₀ u₀ q⁻¹)⁻¹
    have hq : map F U₀ P₀ u₀ u * map F L₀ P₀ l₀ m = q := by
      have hh := congrArg Inv.inv (leviComponent_mul_radicalComponent l₀ u₀
        (q⁻¹ : AdelicGroupPoints F P₀))
      change (map F L₀ P₀ l₀ (leviComponent l₀ u₀ q⁻¹) *
        map F U₀ P₀ u₀ (radicalComponent l₀ u₀ q⁻¹))⁻¹ = q⁻¹⁻¹ at hh
      rw [mul_inv_rev, inv_inv, ← map_inv, ← map_inv] at hh
      exact hh
    have hL : map F P₀ L₀ L q = m := by
      rw [← hq, map_mul]
      change ((u ≫ (u₀).hom.hom) ≫ L.hom.hom) * ((m ≫ (l₀).hom.hom) ≫ L.hom.hom) = m
      simp only [L, comp_leviRetraction, leviComponent_comp_radical, leviComponent_comp_levi, one_mul]
    have hχ₂eval : character F P₀ χ₂.toMul q = character F P₀ χ₁.toMul (map F L₀ P₀ b m) := by
      rw [← hL, ← map_comp_apply_of_hom, character_comp_eval]
    have hqG : map F P₀ G p₀ q = map F U₀ G (Standard.unipotentHom i ν ∅) u *
        map F L₀ G (Standard.leviHom i ν ∅) m := by
      rw [← hq, map_mul, ← map_comp_apply_of_hom, ← map_comp_apply_of_hom,
        Standard.unipotentToParabolic_comp, Standard.leviToParabolic_comp]
    have hM := adelicMatrix_Levi_column_eq σ a hσP n b hb m
    rw [hχ] at hM
    change (adelicMatrix F G σ (map F L₀ G (Standard.leviHom i ν ∅) m)).val *ᵥ
      ((adelicMatrix F G σ (aPoint n.val)).val *ᵥ (Pi.single a 1 : Fin d → Adeles F)) = _ at hM
    rw [hv₂A] at hM
    rw [hqG, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul,
      Pi.smul_apply, smul_eq_mul, adelicMatrix_unipotent_column_sameWeight hG hi σ e heq v₂ j' hv₂supp' u,
      hχ₂eval]
  obtain ⟨C, hC, hcmp⟩ := exists_heightCharacter_le_add_of_orbit_eq hK σ hv₁ j' hj' χ₁ χ₂ h1 h2
  refine ⟨χ₂, C, hC, hχ₂, fun v x => hcmp x _ ?_⟩
  rw [← hv₂A, ← hv₁A, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  have heq : (aPoint n.val * (v : A) * x)⁻¹ * aPoint n.val = x⁻¹ * (v : A)⁻¹ := by group
  rw [heq, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := v.2
  change map F U₀ G (Standard.unipotentHom i ν ∅) u = v.val at hu
  let u' : AdelicGroupPoints F U₀ := u
  have hu' : (v : A)⁻¹ = map F P₀ G p₀ (map F U₀ P₀ u₀ u'⁻¹) := by
    rw [← map_comp_apply_of_hom, Standard.unipotentToParabolic_comp, map_inv]
    exact congrArg Inv.inv hu.symm
  have hunit : character F P₀ χ₁.toMul (map F U₀ P₀ u₀ u'⁻¹) = 1 := by
    have hz := hS.2.2.1.1.isUnipotent.rationalCharacter_eq_zero (characterRestrict u₀ χ₁)
    rw [character_comp_eval, hz]
    exact characterUnits_zero F U₀ A₀ u'⁻¹
  rw [hu', h1, hunit, Units.val_one, one_smul]

end Langlands.Global.ArthurTruncation.Idempotence
