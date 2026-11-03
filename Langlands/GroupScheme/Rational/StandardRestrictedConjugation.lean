import Langlands.GroupScheme.Rational.StandardLeviAnnihilatorTransport

/-! # Restricted standard subgroup transport by actual character images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- Restrict an actual group-scheme isomorphism using an equality of subgroup functors. -/
private def carrierEquivOfComapIso {S : Scheme.{u}} {H G : GroupScheme S}
    (e : H ≅ G) {F0 : SubgroupFunctor H} {F1 : SubgroupFunctor G}
    (hF : F0 = F1.comap e.hom) (U : Over S) : F0.carrier U ≃* F1.carrier U where
  toFun x := ⟨x.1 ≫ e.hom.hom.hom, by
    exact (le_of_eq hF) U x.2⟩
  invFun x := ⟨x.1 ≫ e.inv.hom.hom, by
    rw [hF, mem_comap, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]
    exact x.2⟩
  left_inv x := Subtype.ext (by
    change (x.1 ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x.1
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id])
  right_inv x := Subtype.ext (by
    change (x.1 ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x.1
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id])
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.1 y.1 _)

end SubgroupFunctor

namespace Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Adding a cocharacter that centralizes a point leaves its orbit unchanged. -/
theorem orbit_add_of_mem_centralizer (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) {U : Over S} (g : U ⟶ G.X)
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier U) :
    orbit (CommGroupScheme.groupHom (zeta + eta) ≫ i) g =
      orbit (CommGroupScheme.groupHom zeta ≫ i) g := by
  let a := snd U (Gm S).X ≫ (CommGroupScheme.groupHom zeta ≫ i).hom.hom
  let b := snd U (Gm S).X ≫ (CommGroupScheme.groupHom eta ≫ i).hom.hom
  have hab : snd U (Gm S).X ≫
      (CommGroupScheme.groupHom (zeta + eta) ≫ i).hom.hom = a * b := by
    dsimp [a, b]
    rw [← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    rfl
  calc
    orbit (CommGroupScheme.groupHom (zeta + eta) ≫ i) g =
        a * orbit (CommGroupScheme.groupHom eta ≫ i) g * a⁻¹ := by
      rw [orbit, hab, orbit]
      change (a * b) * _ * (a * b)⁻¹ = a * (b * _ * b⁻¹) * a⁻¹
      group
    _ = orbit (CommGroupScheme.groupHom zeta ≫ i) g := by
      rw [(mem_centralizer _).mp hg]
      rfl

/-- The same orbit extensions witness membership after a centralizing addition. -/
theorem mem_parabolic_add_iff_of_mem_centralizer (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) {U : Over S} (g : U ⟶ G.X)
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier U) :
    g ∈ (parabolic (CommGroupScheme.groupHom (zeta + eta) ≫ i)).carrier U ↔
      g ∈ (parabolic (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [mem_parabolic, IsOrbitExtension, orbit_add_of_mem_centralizer i zeta eta g hg]

/-- A centralizing addition also preserves the value of every orbit extension at zero. -/
theorem mem_unipotent_add_iff_of_mem_centralizer (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) {U : Over S} (g : U ⟶ G.X)
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier U) :
    g ∈ (unipotent (CommGroupScheme.groupHom (zeta + eta) ≫ i)).carrier U ↔
      g ∈ (unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier U := by
  simp only [mem_unipotent, HasLimit, IsOrbitExtension,
    orbit_add_of_mem_centralizer i zeta eta g hg]

end Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Positivity already correct on a face can be extended to all simple roots
by adding a sufficiently large multiple of a standard cocharacter of that face. -/
theorem IsStandardCocharacter.exists_add_zsmul_of_face
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I J : Set (characterLattice T)} (hIJ : I ⊆ J)
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν J zeta)
    (eta : cocharacterLattice T)
    (hzero : ∀ α ∈ I, latticePairing T α eta = 0)
    (hpos : ∀ α ∈ J, α ∉ I → 0 < latticePairing T α eta) :
    ∃ m : ℤ, IsStandardCocharacter i ν I (eta + m • zeta) := by
  obtain ⟨b, hb⟩ := (hfinite.image (fun α => -latticePairing T α eta)).bddAbove
  let m : ℤ := max b 0 + 1
  have hm : 0 ≤ m := by dsimp [m]; omega
  refine ⟨m, hIJ.trans hzeta.1, ?_, ?_⟩
  · intro α hα
    simp only [map_add, map_smul, hzero α hα, hzeta.2.1 α (hIJ hα),
      smul_zero, add_zero]
  · intro α hα hαI
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hαJ : α ∈ J
    · rw [hzeta.2.1 α hαJ, mul_zero, add_zero]
      exact hpos α hαJ hαI
    · have hbound : -latticePairing T α eta ≤ b := hb ⟨α, hα, rfl⟩
      have hpositive : 0 < latticePairing T α zeta := hzeta.2.2 α hα hαJ
      have hmul : m ≤ m * latticePairing T α zeta := by
        have hle : (1 : ℤ) ≤ latticePairing T α zeta := by omega
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hm
      dsimp [m] at hmul ⊢
      omega

/-- Exact images of the face and its boundary preserve all the relevant
zero and strict-positive pairings. -/
theorem cocharacterAut_face_pairing_iff (σ : T ≅ T)
    {I0 I1 J0 J1 : Set (characterLattice T)}
    (hI : characterAut σ '' I0 = I1) (hJ : characterAut σ '' J0 = J1)
    (eta : cocharacterLattice T) :
    ((∀ α ∈ I1, latticePairing T α (cocharacterAut σ eta) = 0) ∧
      ∀ α ∈ J1, α ∉ I1 → 0 < latticePairing T α (cocharacterAut σ eta)) ↔
    ((∀ α ∈ I0, latticePairing T α eta = 0) ∧
      ∀ α ∈ J0, α ∉ I0 → 0 < latticePairing T α eta) := by
  rw [annihilates_image_iff σ hI]
  have hmem (α : characterLattice T) :
      characterAut σ α ∈ I1 ↔ α ∈ I0 := by
    rw [← hI, (characterAut σ).injective.mem_set_image]
  constructor
  · rintro ⟨hzero, hpos⟩
    refine ⟨hzero, fun α hα hαI => ?_⟩
    have h := hpos (characterAut σ α) (hJ ▸ Set.mem_image_of_mem _ hα)
      (fun hα' => hαI ((hmem α).mp hα'))
    rwa [latticePairing_characterAut_cocharacterAut] at h
  · rintro ⟨hzero, hpos⟩
    refine ⟨hzero, ?_⟩
    intro α hα hαI
    obtain ⟨β, hβ, rfl⟩ := hJ.symm ▸ hα
    rw [latticePairing_characterAut_cocharacterAut]
    exact hpos β hβ (fun hβI => hαI ((hmem β).mpr hβI))

section Transport

variable [Mono i.hom.hom.left]

/-- The common orbit argument for the parabolic and identity-limit families. -/
private theorem mem_standardFamily_conj_iff
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
    (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
    (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
    (n : normalizerPoints i)
    (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1)
    (F : cocharacterLattice T → SubgroupFunctor G)
    (hadd : ∀ (eta xi : cocharacterLattice T) {U : Over (Spec (CommRingCat.of k))}
      (g : U ⟶ G.X),
      g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom xi ≫ i)).carrier U →
      (g ∈ (F (eta + xi)).carrier U ↔ g ∈ (F eta).carrier U))
    (hconj : ∀ eta, F eta =
      (F (cocharacterAut (normalizingAut i n) eta)).comap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom)
    {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X)
    (hg0 : g ∈ (standardLevi i ν J0).carrier U)
    (hg1 : g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
      (standardLevi i ν J1).carrier U) :
    (∀ eta, IsStandardCocharacter i ν I0 eta → g ∈ (F eta).carrier U) ↔
    (∀ eta, IsStandardCocharacter i ν I1 eta →
      g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈ (F eta).carrier U) := by
  let σ := normalizingAut i n
  let f := (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom
  obtain ⟨zeta0, hzeta0⟩ := hJ0
  obtain ⟨zeta1, hzeta1⟩ := hJ1
  have hface := cocharacterAut_face_pairing_iff σ hI hJ
  have hcent0 (m : ℤ) :
      g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom (m • zeta0) ≫ i)).carrier U :=
    (Dynamic.centralizingCocharacters i g).smul_mem m
      ((mem_standardLevi i ν).mp hg0 zeta0 hzeta0)
  have hcent1 (m : ℤ) :
      g ≫ f.hom.hom ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom (m • zeta1) ≫ i)).carrier U :=
    (Dynamic.centralizingCocharacters i (g ≫ f.hom.hom)).smul_mem m
      ((mem_standardLevi i ν).mp hg1 zeta1 hzeta1)
  constructor
  · intro hg eta1 heta1
    obtain ⟨eta0, rfl⟩ := (cocharacterAut σ).surjective eta1
    have hsign := (hface eta0).mp
      ⟨heta1.2.1, fun α hα hαI => heta1.2.2 α (hzeta1.1 hα) hαI⟩
    obtain ⟨m, hm⟩ := hzeta0.exists_add_zsmul_of_face i ν hfinite hI0
      eta0 hsign.1 hsign.2
    have h := (hadd eta0 (m • zeta0) g (hcent0 m)).mp (hg _ hm)
    rwa [hconj eta0, SubgroupFunctor.mem_comap] at h
  · intro hg eta0 heta0
    have hsign := (hface eta0).mpr
      ⟨heta0.2.1, fun α hα hαI => heta0.2.2 α (hzeta0.1 hα) hαI⟩
    obtain ⟨m, hm⟩ := hzeta1.exists_add_zsmul_of_face i ν hfinite hI1
      (cocharacterAut σ eta0) hsign.1 hsign.2
    have h := (hadd (cocharacterAut σ eta0) (m • zeta1)
      (g ≫ f.hom.hom) (hcent1 m)).mp (hg _ hm)
    rw [hconj eta0, SubgroupFunctor.mem_comap]
    exact h

/-- Inside the source standard Levi, exact images of the two character sets
transport both positive orbit-extension and identity-limit conditions. -/
theorem mem_standardParabolic_unipotent_conj_iff_of_character_images
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
    (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
    (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
    (n : normalizerPoints i)
    (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1)
    {U : Over (Spec (CommRingCat.of k))} (g : U ⟶ G.X)
    (hg0 : g ∈ (standardLevi i ν J0).carrier U) :
    (g ∈ (standardParabolic i ν I0).carrier U ↔
      g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
        (standardParabolic i ν I1).carrier U) ∧
    (g ∈ (standardUnipotent i ν I0).carrier U ↔
      g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
        (standardUnipotent i ν I1).carrier U) := by
  have hg1 : g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
      (standardLevi i ν J1).carrier U := by
    have h := hg0
    rwa [standardLevi_eq_comap_of_finite_of_exists i ν hfinite hJ1 hJ0 n hJ,
      SubgroupFunctor.mem_comap] at h
  constructor
  · simp only [mem_standardParabolic]
    apply mem_standardFamily_conj_iff i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ
      (fun eta => Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i))
      (fun eta xi _ g hg => Dynamic.mem_parabolic_add_iff_of_mem_centralizer i eta xi g hg)
      _ g hg0 hg1
    intro eta
    rw [groupHom_cocharacterAut_comp]
    exact Dynamic.parabolic_eq_comap_of_iso _ _
  · simp only [mem_standardUnipotent]
    apply mem_standardFamily_conj_iff i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ
      (fun eta => Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i))
      (fun eta xi _ g hg => Dynamic.mem_unipotent_add_iff_of_mem_centralizer i eta xi g hg)
      _ g hg0 hg1
    intro eta
    rw [groupHom_cocharacterAut_comp]
    exact Dynamic.unipotent_eq_comap_of_iso _ _

/-- Literal restricted standard P/U functors conjugate under exact character
images. Finiteness and standard-cocharacter existence are the only root-structure inputs. -/
theorem restrictedStandardSubgroups_eq_comap_of_character_images
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
    (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
    (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
    (n : normalizerPoints i)
    (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1) :
    (standardLevi i ν J0 ⊓ standardParabolic i ν I0) =
      (standardLevi i ν J1 ⊓ standardParabolic i ν I1).comap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom ∧
    (standardLevi i ν J0 ⊓ standardUnipotent i ν I0) =
      (standardLevi i ν J1 ⊓ standardUnipotent i ν I1).comap
        (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  have hLevi := standardLevi_eq_comap_of_finite_of_exists i ν hfinite hJ1 hJ0 n hJ
  have hmem (U : Over (Spec (CommRingCat.of k))) :=
    mem_standardParabolic_unipotent_conj_iff_of_character_images i ν (U := U)
    hfinite hI0 hI1 hJ0 hJ1 n hI hJ
  constructor
  · apply SubgroupFunctor.ext
    intro U
    apply Subgroup.ext
    intro g
    have hL : g ∈ (standardLevi i ν J0).carrier U ↔
        g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
          (standardLevi i ν J1).carrier U := by
      rw [hLevi, SubgroupFunctor.mem_comap]
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hgL, hgP⟩
      exact ⟨hL.mp hgL, (hmem U g hgL).1.mp hgP⟩
    · rintro ⟨hgL, hgP⟩
      have hg0 := hL.mpr hgL
      exact ⟨hg0, (hmem U g hg0).1.mpr hgP⟩
  · apply SubgroupFunctor.ext
    intro U
    apply Subgroup.ext
    intro g
    have hL : g ∈ (standardLevi i ν J0).carrier U ↔
        g ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom.hom.hom ∈
          (standardLevi i ν J1).carrier U := by
      rw [hLevi, SubgroupFunctor.mem_comap]
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hgL, hgP⟩
      exact ⟨hL.mp hgL, (hmem U g hgL).2.mp hgP⟩
    · rintro ⟨hgL, hgP⟩
      have hg0 := hL.mpr hgL
      exact ⟨hg0, (hmem U g hg0).2.mpr hgP⟩

/-- The actual conjugation equivalence for the restricted standard parabolic,
over every test scheme. -/
def restrictedStandardParabolicConjEquiv
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
    (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
    (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
    (n : normalizerPoints i)
    (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1)
    (U : Over (Spec (CommRingCat.of k))) :
    (standardLevi i ν J0 ⊓ standardParabolic i ν I0).carrier U ≃*
      (standardLevi i ν J1 ⊓ standardParabolic i ν I1).carrier U :=
  SubgroupFunctor.carrierEquivOfComapIso
    (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X))
    (restrictedStandardSubgroups_eq_comap_of_character_images i ν
      hfinite hI0 hI1 hJ0 hJ1 n hI hJ).1 U

/-- The actual conjugation equivalence for the restricted standard unipotent functor,
over every test scheme. -/
def restrictedStandardUnipotentConjEquiv
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
    (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
    (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
    (n : normalizerPoints i)
    (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1)
    (U : Over (Spec (CommRingCat.of k))) :
    (standardLevi i ν J0 ⊓ standardUnipotent i ν I0).carrier U ≃*
      (standardLevi i ν J1 ⊓ standardUnipotent i ν I1).carrier U :=
  SubgroupFunctor.carrierEquivOfComapIso
    (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X))
    (restrictedStandardSubgroups_eq_comap_of_character_images i ν
      hfinite hI0 hI1 hJ0 hJ1 n hI hJ).2 U

section Formulas

variable (hfinite : (simpleRelativeRoots i ν).Finite)
  {I0 I1 J0 J1 : Set (characterLattice T)} (hI0 : I0 ⊆ J0) (hI1 : I1 ⊆ J1)
  (hJ0 : ∃ zeta, IsStandardCocharacter i ν J0 zeta)
  (hJ1 : ∃ zeta, IsStandardCocharacter i ν J1 zeta)
  (n : normalizerPoints i)
  (hI : weylAction i n '' I0 = I1) (hJ : weylAction i n '' J0 = J1)
  (U : Over (Spec (CommRingCat.of k)))

@[simp] theorem restrictedStandardParabolicConjEquiv_apply
    (x : (standardLevi i ν J0 ⊓ standardParabolic i ν I0).carrier U) :
    (restrictedStandardParabolicConjEquiv i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ U x :
      U ⟶ G.X) = G.constantPoint n U * x.1 * (G.constantPoint n U)⁻¹ :=
  comp_innerIso_hom G n U x.1

@[simp] theorem restrictedStandardUnipotentConjEquiv_apply
    (x : (standardLevi i ν J0 ⊓ standardUnipotent i ν I0).carrier U) :
    (restrictedStandardUnipotentConjEquiv i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ U x :
      U ⟶ G.X) = G.constantPoint n U * x.1 * (G.constantPoint n U)⁻¹ :=
  comp_innerIso_hom G n U x.1

@[simp] theorem restrictedStandardParabolicConjEquiv_symm_apply
    (x : (standardLevi i ν J1 ⊓ standardParabolic i ν I1).carrier U) :
    ((restrictedStandardParabolicConjEquiv i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ U).symm x :
      U ⟶ G.X) = (G.constantPoint n U)⁻¹ * x.1 * G.constantPoint n U := by
  change x.1 ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv.hom.hom = _
  rw [← G.innerIso_inv_hom, comp_innerIso_hom, G.constantPoint_inv, inv_inv]

@[simp] theorem restrictedStandardUnipotentConjEquiv_symm_apply
    (x : (standardLevi i ν J1 ⊓ standardUnipotent i ν I1).carrier U) :
    ((restrictedStandardUnipotentConjEquiv i ν hfinite hI0 hI1 hJ0 hJ1 n hI hJ U).symm x :
      U ⟶ G.X) = (G.constantPoint n U)⁻¹ * x.1 * G.constantPoint n U := by
  change x.1 ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv.hom.hom = _
  rw [← G.innerIso_inv_hom, comp_innerIso_hom, G.constantPoint_inv, inv_inv]

include hfinite hI0 hI1 hJ0 hJ1 hI hJ

/-- Target-Levi membership gives the inverse-conjugation tests for both families. -/
theorem mem_standardParabolic_unipotent_inv_conj_iff_of_character_images
    (x : U ⟶ G.X) (hx : x ∈ (standardLevi i ν J1).carrier U) :
    (x ∈ (standardParabolic i ν I1).carrier U ↔
      (G.constantPoint n U)⁻¹ * x * G.constantPoint n U ∈
        (standardParabolic i ν I0).carrier U) ∧
    (x ∈ (standardUnipotent i ν I1).carrier U ↔
      (G.constantPoint n U)⁻¹ * x * G.constantPoint n U ∈
        (standardUnipotent i ν I0).carrier U) := by
  let y := (G.constantPoint n U)⁻¹ * x * G.constantPoint n U
  have heq : G.constantPoint n U * y * (G.constantPoint n U)⁻¹ = x := by
    dsimp [y]
    group
  have hy : y ∈ (standardLevi i ν J0).carrier U := by
    rw [standardLevi_eq_comap_of_finite_of_exists i ν hfinite hJ1 hJ0 n hJ,
      SubgroupFunctor.mem_comap, comp_innerIso_hom, heq]
    exact hx
  have h := mem_standardParabolic_unipotent_conj_iff_of_character_images i ν
    hfinite hI0 hI1 hJ0 hJ1 n hI hJ y hy
  rw [comp_innerIso_hom] at h
  rw [heq] at h
  exact ⟨h.1.symm, h.2.symm⟩

end Formulas

end Transport

end Langlands.GroupScheme
