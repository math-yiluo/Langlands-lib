import Langlands.GroupScheme.Rational.StandardLeviAnnihilatorTransport
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Adding a cocharacter centralizing the point preserves its actual orbit. -/
theorem orbit_add_zsmul_of_mem_centralizer (i : T.toGrp ⟶ G)
    (zeta theta : cocharacterLattice T) (m : ℤ)
    {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom theta ≫ i)).carrier U) :
    orbit (CommGroupScheme.groupHom (zeta + m • theta) ≫ i) g =
      orbit (CommGroupScheme.groupHom zeta ≫ i) g := by
  let a := (snd U (Gm S).X ≫ (CommGroupScheme.groupHom zeta).hom.hom) ≫ i.hom.hom
  let b := (snd U (Gm S).X ≫ (CommGroupScheme.groupHom theta).hom.hom) ≫ i.hom.hom
  let x := fst U (Gm S).X ≫ g
  have hx : Commute x (b ^ m) := by
    apply Commute.zpow_right
    exact commute_cocharacter_of_mem_centralizer _
      ((centralizer _).comp_mem (fst U (Gm S).X) hg) (snd U (Gm S).X)
  simp only [orbit, Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add,
    MonObj.mul_comp, comp_groupHom_zsmul, GrpObj.zpow_comp]
  change (a * b ^ m) * x * (a * b ^ m)⁻¹ = a * x * a⁻¹
  calc
    _ = a * (b ^ m * x * (b ^ m)⁻¹) * a⁻¹ := by group
    _ = _ := by rw [hx.symm.eq, mul_inv_cancel_right]

end Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- A cocharacter standard on a nested face becomes globally standard after
adding a sufficiently large multiple of one standard for the outer face. -/
theorem IsStandardCocharacter.exists_add_zsmul_of_nested
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J K : Set (characterLattice T)} (hKJ : K ⊆ J)
    {theta : cocharacterLattice T} (htheta : IsStandardCocharacter i ν J theta)
    (zeta : cocharacterLattice T)
    (hzero : ∀ α ∈ K, latticePairing T α zeta = 0)
    (hpos : ∀ α ∈ J, α ∉ K → 0 < latticePairing T α zeta) :
    ∃ m : ℤ, IsStandardCocharacter i ν K (zeta + m • theta) := by
  obtain ⟨b, hb⟩ := (hfinite.image (fun α => -latticePairing T α zeta)).bddAbove
  let m : ℤ := max b 0 + 1
  have hm : 0 ≤ m := by dsimp [m]; omega
  refine ⟨m, hKJ.trans htheta.1, ?_, ?_⟩
  · intro α hα
    simp only [map_add, map_smul, hzero α hα, htheta.2.1 α (hKJ hα),
      smul_zero, add_zero]
  · intro α hα hαK
    by_cases hαJ : α ∈ J
    · simpa only [map_add, map_smul, htheta.2.1 α hαJ, smul_zero, add_zero]
        using hpos α hαJ hαK
    · have hbound : -latticePairing T α zeta ≤ b := hb ⟨α, hα, rfl⟩
      have hthetaPos := htheta.2.2 α hα hαJ
      have hmul : m ≤ m * latticePairing T α theta := by
        have hle : (1 : ℤ) ≤ latticePairing T α theta := by omega
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hm
      simp only [map_add, map_smul, smul_eq_mul]
      dsimp [m] at hmul ⊢
      omega

/-- On an associated Levi, conjugation carries the unipotent radical for a
nested standard face to the radical for its transported face. -/
theorem mem_standardUnipotent_conj_of_mem_standardLevi
    [Mono i.hom.hom.left]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J J' K K' : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hJ' : J' ⊆ simpleRelativeRoots i ν)
    (hKJ : K ⊆ J) (hK'J' : K' ⊆ J')
    (n : normalizerPoints i)
    (hJJ' : weylAction i n '' J = J')
    (hKK' : weylAction i n '' K = K')
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X}
    (hg : g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
      (standardLevi i ν J').carrier U) :
    g ∈ (standardUnipotent i ν K).carrier U ↔
      g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
        (standardUnipotent i ν K').carrier U := by
  let std := hStandard k G hG T i hi ν hν
  obtain ⟨zeta, hzeta⟩ := (std K (hKJ.trans hJ)).1
  obtain ⟨theta, htheta⟩ := (std J' hJ').1
  let eta := cocharacterAut (normalizingAut i n) zeta
  have hzero : ∀ α ∈ K', latticePairing T α eta = 0 := by
    intro α hα
    obtain ⟨β, hβ, rfl⟩ := hKK'.symm ▸ hα
    change latticePairing T (characterAut (normalizingAut i n) β)
      (cocharacterAut (normalizingAut i n) zeta) = 0
    rw [latticePairing_characterAut_cocharacterAut]
    exact hzeta.2.1 β hβ
  have hpos : ∀ α ∈ J', α ∉ K' → 0 < latticePairing T α eta := by
    intro α hα hαK'
    obtain ⟨β, hβ, rfl⟩ := hJJ'.symm ▸ hα
    change 0 < latticePairing T (characterAut (normalizingAut i n) β)
      (cocharacterAut (normalizingAut i n) zeta)
    rw [latticePairing_characterAut_cocharacterAut]
    apply hzeta.2.2 β (hJ hβ)
    intro hβK
    exact hαK' (hKK' ▸ Set.mem_image_of_mem _ hβK)
  obtain ⟨m, hm⟩ := htheta.exists_add_zsmul_of_nested i ν hfinite hK'J' eta hzero hpos
  have horbit := Dynamic.orbit_add_zsmul_of_mem_centralizer i eta theta m
    (standardLevi_le_dynamicCentralizer i ν htheta U hg)
  have hsum :
      g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom (eta + m • theta) ≫ i)).carrier U ↔
        g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
          (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier U := by
    simp only [Dynamic.mem_unipotent, Dynamic.HasLimit, Dynamic.IsOrbitExtension, horbit]
  rw [(std K (hKJ.trans hJ)).2 zeta hzeta |>.2.2,
    (std K' (hK'J'.trans hJ')).2 (eta + m • theta) hm |>.2.2]
  rw [hsum, groupHom_cocharacterAut_comp]
  exact Iff.rfl.trans (by
    rw [← SubgroupFunctor.mem_comap,
      ← Dynamic.unipotent_eq_comap_of_iso _ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X))])

end Langlands.GroupScheme
