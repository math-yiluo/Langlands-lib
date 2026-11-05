import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.GroupScheme.Rational.LocalFieldDensity
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.GroupScheme.Dynamic.ParabolicProduct

/-! # Chamber generation from opposite cells over the local field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

private theorem point_comp_mulRight (a g : rationalPoints G) :
    a ≫ (GrpObj.mulRight g).hom = a * g := by
  change a ≫ ((𝟙 G.X) * (toUnit G.X ≫ g)) = a * g
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc]
  have h : a ≫ toUnit G.X = 𝟙 _ := toUnit_unique _ _
  rw [h, Category.id_comp]

/-- In a group with dense rational points and irreducible underlying scheme,
every rational translation carries some rational point of an open cell
to another rational point of that same cell. -/
theorem exists_cell_points_mul_eq_of_dense
    [IrreducibleSpace G.X.left] (hdense : HasDenseRationalPoints k G.X)
    {X : Over (Spec (CommRingCat.of k))} (f : X ⟶ G.X)
    [IsOpenImmersion f.left] (x₀ : RationalPoint k X) (g : rationalPoints G) :
    ∃ x y : RationalPoint k X, (x ≫ f) * g = y ≫ f := by
  let e := GrpObj.mulRight g
  let Ω : Set G.X.left := Set.range f.left
  have hΩ : IsOpen Ω := IsOpenImmersion.isOpen_range f.left
  have hΩne : Ω.Nonempty :=
    ⟨f.left (x₀.left (IsLocalRing.closedPoint k)), ⟨_, rfl⟩⟩
  have hpre : IsOpen (e.hom.left ⁻¹' Ω) := hΩ.preimage e.hom.left.continuous
  have hprene : (e.hom.left ⁻¹' Ω).Nonempty := by
    obtain ⟨z, hz⟩ := hΩne
    obtain ⟨w, hw⟩ := (Scheme.homeoOfIso ((Over.forget _).mapIso e)).surjective z
    change e.hom.left w = z at hw
    exact ⟨w, by change e.hom.left w ∈ Ω; rwa [hw]⟩
  obtain ⟨z, hz, hzΩ, hzgΩ⟩ :=
    hdense.exists_mem_open (hΩ.inter hpre)
      (nonempty_preirreducible_inter hΩ hpre hΩne hprene)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hz
  obtain ⟨s, rfl⟩ := ha
  have haΩ : Set.range a.left ⊆ Set.range f.left := by
    rintro _ ⟨w, rfl⟩
    have hw : w = s := Subsingleton.elim (α := PrimeSpectrum k) w s
    simpa only [hw] using hzΩ
  have hagΩ : Set.range (a * g).left ⊆ Set.range f.left := by
    rintro _ ⟨w, rfl⟩
    have hpt := point_comp_mulRight a g
    rw [← hpt]
    change e.hom.left (a.left w) ∈ Ω
    have hw : w = s := Subsingleton.elim (α := PrimeSpectrum k) w s
    simpa only [hw, Set.mem_preimage] using hzgΩ
  let x : RationalPoint k X :=
    Over.homMk (IsOpenImmersion.lift f.left a.left haΩ) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w a])
  let y : RationalPoint k X :=
    Over.homMk (IsOpenImmersion.lift f.left (a * g).left hagΩ) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w (a * g)])
  have hx : x ≫ f = a :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac f.left a.left haΩ)
  have hy : y ≫ f = a * g :=
    Over.OverMorphism.ext (IsOpenImmersion.lift_fac f.left (a * g).left hagΩ)
  exact ⟨x, y, by rw [hx, hy]⟩

end Langlands.GroupScheme

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Dense local-field points and the opposite open cell give the generation
inclusion for any two subgroups containing both complete dynamic radicals. -/
theorem subgroup_le_sup_normalizer_inf_of_localField
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter i ν)
    (R B : Subgroup (rationalPoints G))
    (hR : ∀ xi : cocharacterLattice S,
      (Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier (Over.mk (𝟙 _)) ≤ R)
    (hB : ∀ xi : cocharacterLattice S,
      (Dynamic.unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier (Over.mk (𝟙 _)) ≤ B) :
    R ≤ B ⊔ (normalizerPoints i ⊓ R) := by
  have := hG.smooth
  have := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have := CharacterLatticeProof.isIntegral_of_smooth F G.X.hom
  have : IrreducibleSpace G.X.left := inferInstance
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χ' := CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ
  have hnegative : CommGroupScheme.groupHom (-ν) ≫ i = χ' := by
    have hneg : Gm.powerHom _ (-1) ≫ ν = -ν := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    dsimp only [χ', χ]
    rw [← Category.assoc]
    change CommGroupScheme.groupHom (-ν) ≫ i =
      CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ i
    rw [hneg]
  let O := Dynamic.Affine.unipotentScheme χ'
  let P := Dynamic.Affine.parabolicScheme χ
  let jO := Dynamic.Affine.unipotentHom χ'
  let jP := Dynamic.Affine.parabolicHom χ
  have hO : (Dynamic.unipotent χ').IsRepresentedBy jO :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hP : (Dynamic.parabolic χ).IsRepresentedBy jP :=
    Dynamic.Affine.isRepresentedBy_parabolicHom χ
  let f : O.X ⊗ P.X ⟶ G.X := (fst _ _ ≫ jO.hom.hom) * (snd _ _ ≫ jP.hom.hom)
  have : IsOpenImmersion f.left := oppositeCellStatement F G χ O P jO jP hO hP
  have hdec (t : RationalPoint F (O.X ⊗ P.X)) :
      ∃ a ∈ (Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)),
        ∃ z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)),
          ∃ b ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)),
            t ≫ f = a * z * b := by
    let a := t ≫ fst O.X P.X ≫ jO.hom.hom
    let p := t ≫ snd O.X P.X ≫ jP.hom.hom
    have ha : a ∈ (Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) :=
      (hO.pointsEquiv _ (t ≫ fst O.X P.X)).property
    have hp : p ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) :=
      (hP.pointsEquiv _ (t ≫ snd O.X P.X)).property
    let z := Dynamic.limit χ ⟨p, hp⟩
    refine ⟨a, ha, z, Dynamic.limit_mem_centralizer χ ⟨p, hp⟩,
      z⁻¹ * p, Dynamic.inv_limit_mul_mem_unipotent χ ⟨p, hp⟩, ?_⟩
    change t ≫ ((fst _ _ ≫ jO.hom.hom) * (snd _ _ ≫ jP.hom.hom)) = a * z * (z⁻¹ * p)
    rw [MonObj.comp_mul]
    change a * p = a * z * (z⁻¹ * p)
    group
  have hZ := genericCentralizer F G hG S i hi ν hν
  have hZ' : torusCentralizer i ≤ Dynamic.centralizer χ' := by
    dsimp only [χ', χ]
    rw [← Category.assoc]
    exact torusCentralizer_le_dynamicCentralizer i _
  have hRminus : (Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) ≤ R :=
    hnegative ▸ hR (-ν)
  have hBminus : (Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) ≤ B :=
    hnegative ▸ hB (-ν)
  intro g hg
  obtain ⟨x, y, hxy⟩ := exists_cell_points_mul_eq_of_dense
    (hasDenseRationalPoints_of_localField F G) f (lift 1 1) g
  obtain ⟨a, ha, z, hz, b, hb, hx⟩ := hdec x
  obtain ⟨c, hc, z', hz', d, hd, hy⟩ := hdec y
  have hzT : z ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := hZ ▸ hz
  have hz'T : z' ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := hZ ▸ hz'
  let v := z⁻¹ * (a⁻¹ * c) * z
  let n := z⁻¹ * z'
  have hv : v ∈ (Dynamic.unipotent χ').carrier (Over.mk (𝟙 _)) := by
    have hzi := ((torusCentralizer i).carrier (Over.mk (𝟙 _))).inv_mem hzT
    have h := Dynamic.conj_mem_unipotent χ'
      (Dynamic.centralizer_le_parabolic χ' _ (hZ' _ hzi))
      (((Dynamic.unipotent χ').carrier _).mul_mem
        (((Dynamic.unipotent χ').carrier _).inv_mem ha) hc)
    simpa only [inv_inv] using h
  have hnN : n ∈ normalizerPoints i := by
    apply centralizerPoints_le_normalizerPoints i
    rw [← torusCentralizer_carrier_base]
    exact ((torusCentralizer i).carrier _).mul_mem
      (((torusCentralizer i).carrier _).inv_mem hzT) hz'T
  have heq : g = b⁻¹ * v * n * d := by
    rw [hx, hy] at hxy
    have heq' : g = (a * z * b)⁻¹ * (c * z' * d) :=
      (eq_inv_mul_iff_mul_eq).mpr hxy
    rw [heq']
    dsimp only [v, n]
    group
  have hnR : n ∈ R := by
    have hn : n = (b⁻¹ * v)⁻¹ * g * d⁻¹ := by rw [heq]; group
    rw [hn]
    exact R.mul_mem (R.mul_mem
      (R.inv_mem (R.mul_mem (R.inv_mem (hR ν hb)) (hRminus hv))) hg)
      (R.inv_mem (hR ν hd))
  have hBL : B ≤ B ⊔ (normalizerPoints i ⊓ R) := le_sup_left
  have hNL : normalizerPoints i ⊓ R ≤ B ⊔ (normalizerPoints i ⊓ R) := le_sup_right
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hBL (B.inv_mem (hB ν hb))) (hBL (hBminus hv)))
    (hNL ⟨hnN, hnR⟩)) (hBL (hB ν hd))

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The actual chamber-generation conclusion from containment of complete
dynamic radicals, using the proved local-field density theorem. -/
theorem zeroSubgroup_le_chamber_sup_of_dynamicRadicals
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (C : Set P.Apartment)
    (hU : ∀ ν : cocharacterLattice P.S,
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier (Over.mk (𝟙 _)) ≤
        P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)) :
    P.zeroSubgroup ≤ P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup) := by
  have := P.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ := P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  let K := P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)
  have hK : K ≤ P.zeroSubgroup := sup_le (P.parahoric_le_zeroSubgroup hA C) inf_le_right
  have hgen := subgroup_le_sup_normalizer_inf_of_localField P.isConnectedReductive
    P.isMaximalSplitTorus ν hν P.zeroSubgroup K
    (fun xi => (hU xi).trans hK) hU
  exact hgen.trans (sup_le le_rfl le_sup_right)

end Langlands.Geometry.Building.ParahoricBuildingData
