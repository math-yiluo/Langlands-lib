import Langlands.GroupScheme.Rational.RationalLeviConjugacyStatement
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.GeometricUnipotentRadicalComparison
import Langlands.GroupScheme.Rational.PointDecomposition
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalStatement
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Rational Levi conjugacy from dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicLeviConjugacy

section Base

variable {S : Scheme.{u}} {G P L : GroupScheme S}

/-- The points of a cocharacter lie in its dynamic parabolic. -/
theorem range_le_parabolic (χ : (Gm S).toGrp ⟶ G) :
    SubgroupFunctor.range χ ≤ Dynamic.parabolic χ := by
  have h := range_le_torusCentralizer χ
  rw [torusCentralizer_gm_eq_dynamicCentralizer] at h
  exact h.trans (Dynamic.centralizer_le_parabolic χ)

variable (χ : (Gm S).toGrp ⟶ G) {j : P ⟶ G} (hj : (Dynamic.parabolic χ).IsRepresentedBy j)

/-- The cocharacter, factored through a representative of its dynamic parabolic. -/
def parabolicCocharacter : (Gm S).toGrp ⟶ P :=
  hj.factorHom χ (range_le_parabolic χ)

theorem parabolicCocharacter_comp : parabolicCocharacter χ hj ≫ j = χ :=
  hj.factorHom_comp χ (range_le_parabolic χ)

include hj in
theorem mem_parabolic_comp {T : Over S} (x : T ⟶ P.X) :
    x ≫ j.hom.hom ∈ (Dynamic.parabolic χ).carrier T := by
  rw [← hj.2]
  exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩

include hj in
theorem exists_comp_eq_of_mem_parabolic {T : Over S} {y : T ⟶ G.X}
    (hy : y ∈ (Dynamic.parabolic χ).carrier T) : ∃ x : T ⟶ P.X, x ≫ j.hom.hom = y := by
  rw [← hj.2] at hy
  exact SubgroupFunctor.mem_range.mp hy

variable {χ} {hj} (l : L ⟶ P) (q : P ⟶ L) (hlq : l ≫ q = 𝟙 L)
  (hker : ∀ (T : Over S) (x : T ⟶ P.X),
    x ≫ q.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T)

include hlq in
theorem hom_hom_comp_hom_hom : l.hom.hom ≫ q.hom.hom = 𝟙 L.X := by
  rw [← Grp.comp_hom_hom, hlq, Grp.id_hom_hom]

include hlq hker in
/-- The image of the cocharacter in the Levi factor is central. -/
theorem centralizer_leviCocharacter_eq_top [IsSeparated G.X.hom] :
    Dynamic.centralizer (parabolicCocharacter χ hj ≫ q) = ⊤ := by
  have : Mono j.hom.hom := hj.1
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun y => iff_of_true ?_ (Subgroup.mem_top _)
  have hp := mem_parabolic_comp χ hj (y ≫ l.hom.hom)
  have hz := Dynamic.limit_mem_centralizer χ ⟨_, hp⟩
  have hzu := Dynamic.mul_inv_limit_mem_unipotent χ ⟨_, hp⟩
  obtain ⟨zP, hzP⟩ := exists_comp_eq_of_mem_parabolic χ hj
    (Dynamic.centralizer_le_parabolic χ T hz)
  have hzc : zP ∈ (Dynamic.centralizer (parabolicCocharacter χ hj)).carrier T := by
    rw [Dynamic.centralizer_eq_comap_of_mono (parabolicCocharacter χ hj) j,
      parabolicCocharacter_comp, SubgroupFunctor.mem_comap, hzP]
    exact hz
  have hzq := Dynamic.centralizer_le_comap (parabolicCocharacter χ hj) q T hzc
  rw [SubgroupFunctor.mem_comap] at hzq
  have hw : (y ≫ l.hom.hom * zP⁻¹) ≫ q.hom.hom = 1 := by
    rw [hker, MonObj.mul_comp, GrpObj.inv_comp, hzP]
    exact hzu
  rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc,
    hom_hom_comp_hom_hom l q hlq, Category.comp_id] at hw
  rw [hw]
  exact hzq

include hlq hker in
/-- The Levi cocharacter differs from the cocharacter by a point of `U(χ)`. -/
theorem leviCocharacter_mul_inv_mem :
    ((parabolicCocharacter χ hj ≫ q) ≫ l ≫ j).hom.hom * (χ.hom.hom)⁻¹ ∈
      (Dynamic.unipotent χ).carrier (Gm S).X := by
  have hχ : χ.hom.hom = (parabolicCocharacter χ hj).hom.hom ≫ j.hom.hom :=
    (congrArg (fun f : (Gm S).toGrp ⟶ G => f.hom.hom) (parabolicCocharacter_comp χ hj)).symm
  have hql : (q ≫ l).hom.hom ≫ q.hom.hom = q.hom.hom := by
    rw [Grp.comp_hom_hom, Category.assoc, hom_hom_comp_hom_hom l q hlq, Category.comp_id]
  have hw : ((parabolicCocharacter χ hj).hom.hom ≫ (q ≫ l).hom.hom *
      ((parabolicCocharacter χ hj).hom.hom)⁻¹) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hql, mul_inv_cancel]
  rw [hker, MonObj.mul_comp, GrpObj.inv_comp] at hw
  rw [hχ]
  simpa only [Grp.comp_hom_hom, Category.assoc] using hw

include hlq hker in
/-- After conjugation by a point `u` of `U(χ)` transporting `χ` to the Levi cocharacter,
the Levi has exactly the points of `Z(χ)`. -/
theorem range_comp_innerIso_inv_eq_centralizer [IsSeparated G.X.hom]
    {u : Over.mk (𝟙 S) ⟶ G.X} (hu : u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)))
    (hμ : χ ≫ (G.innerIso u).hom = (parabolicCocharacter χ hj ≫ q) ≫ l ≫ j) :
    SubgroupFunctor.range (l ≫ j ≫ (G.innerIso u).inv) = Dynamic.centralizer χ := by
  have hlj : (l ≫ j ≫ (G.innerIso u).inv) ≫ (G.innerIso u).hom = l ≫ j := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hle : SubgroupFunctor.range (l ≫ j ≫ (G.innerIso u).inv) ≤ Dynamic.centralizer χ := by
    intro T z hz
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    rw [Dynamic.centralizer_eq_comap_of_iso χ (G.innerIso u), hμ, SubgroupFunctor.mem_comap]
    have hy : y ∈ (Dynamic.centralizer (parabolicCocharacter χ hj ≫ q)).carrier T := by
      rw [centralizer_leviCocharacter_eq_top l q hlq hker]
      exact Subgroup.mem_top y
    have h := Dynamic.centralizer_le_comap (parabolicCocharacter χ hj ≫ q) (l ≫ j) T hy
    rw [SubgroupFunctor.mem_comap] at h
    convert h using 1
    rw [Category.assoc, ← Grp.comp_hom_hom, hlj]
  refine le_antisymm hle fun T z hz => ?_
  have hcu : G.constantPoint u T ∈ (Dynamic.unipotent χ).carrier T :=
    (Dynamic.unipotent χ).comp_mem _ hu
  have hcu' : G.constantPoint u⁻¹ T ∈ (Dynamic.unipotent χ).carrier T :=
    (Dynamic.unipotent χ).comp_mem _ (inv_mem hu)
  have hz' : z ≫ (G.innerIso u).hom.hom.hom ∈ (Dynamic.parabolic χ).carrier T := by
    rw [comp_innerIso_hom]
    have hcP := Dynamic.unipotent_le_parabolic χ T hcu
    exact mul_mem (mul_mem hcP (Dynamic.centralizer_le_parabolic χ T hz)) (inv_mem hcP)
  obtain ⟨pz, hpz⟩ := exists_comp_eq_of_mem_parabolic χ hj hz'
  have hw : ((pz ≫ q.hom.hom ≫ l.hom.hom)⁻¹ * pz) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc,
      hom_hom_comp_hom_hom l q hlq, Category.comp_id, inv_mul_cancel]
  rw [hker, MonObj.mul_comp, GrpObj.inv_comp, hpz] at hw
  have hw' := mul_mem (mul_mem hcu' hw) (inv_mem hcu')
  rw [← comp_innerIso_hom, innerIso_inv_hom, MonObj.mul_comp, GrpObj.inv_comp,
    Dynamic.comp_hom_hom_comp_inv_hom] at hw'
  have hB : (pz ≫ q.hom.hom) ≫ (l ≫ j ≫ (G.innerIso u).inv).hom.hom ∈
      (Dynamic.centralizer χ).carrier T :=
    hle T (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
  have hZ := mul_mem (inv_mem hB) hz
  have hU : ((pz ≫ q.hom.hom) ≫ (l ≫ j ≫ (G.innerIso u).inv).hom.hom)⁻¹ * z ∈
      (Dynamic.unipotent χ).carrier T := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using hw'
  have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
    (fun _ _ _ _ hl hl' => hl.unique χ hl') hZ hU
  rw [inv_mul_eq_one] at h1
  exact SubgroupFunctor.mem_range.mpr ⟨_, h1⟩

include hlq hker in
/-- A point of the parabolic lying in `U(χ)` whose inner automorphism preserves the Levi
is trivial. -/
theorem eq_one_of_comp_innerIso [IsSeparated G.X.hom]
    {u : Over.mk (𝟙 S) ⟶ G.X} (hu : u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)))
    (hμ : χ ≫ (G.innerIso u).hom = (parabolicCocharacter χ hj ≫ q) ≫ l ≫ j)
    {g : Over.mk (𝟙 S) ⟶ P.X}
    (hg : g ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)))
    (σ : L ≅ L) (hσ : l ≫ (P.innerIso g).hom = σ.hom ≫ l) : g = 1 := by
  have : Mono j.hom.hom := hj.1
  have hgq : g ≫ q.hom.hom = 1 := (hker _ g).2 hg
  have hσ' : σ.hom = 𝟙 L := by
    have h := congrArg (· ≫ q) hσ
    simp only [Category.assoc, innerIso_hom_comp q g, hgq, innerIso_one_hom,
      Category.comp_id, hlq] at h
    exact h.symm
  rw [hσ', Category.id_comp] at hσ
  have hgG : l ≫ j ≫ (G.innerIso (g ≫ j.hom.hom)).hom = l ≫ j := by
    rw [← innerIso_hom_comp j g, ← Category.assoc, hσ]
  have hcent : u⁻¹ * (g ≫ j.hom.hom) * u ∈
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 S)) := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer_base_iff,
      innerIso_mul_hom, innerIso_mul_hom]
    have e1 : χ ≫ (G.innerIso u).hom ≫ (G.innerIso (g ≫ j.hom.hom)).hom ≫
        (G.innerIso u⁻¹).hom =
        (parabolicCocharacter χ hj ≫ q) ≫ (l ≫ j ≫ (G.innerIso (g ≫ j.hom.hom)).hom) ≫
          (G.innerIso u⁻¹).hom := by
      rw [← Category.assoc χ, hμ]
      simp only [Category.assoc]
    rw [e1, hgG, ← Category.assoc (parabolicCocharacter χ hj ≫ q), ← hμ, innerIso_inv_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hunip : u⁻¹ * (g ≫ j.hom.hom) * u ∈
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 S)) :=
    mul_mem (mul_mem (inv_mem hu) hg) hu
  have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
    (fun _ _ _ _ hl hl' => hl.unique χ hl') hcent hunip
  have hx : g ≫ j.hom.hom = 1 := by
    have h2 := congrArg (fun y => u * y * u⁻¹) h1
    simpa [mul_assoc] using h2
  exact (cancel_mono j.hom.hom).mp (hx.trans (MonObj.one_comp _).symm)

end Base

section Field

variable {k : Type u} [Field k]

/-- The specified geometric unipotent radical of a dynamic parabolic of a connected
reductive group has exactly the points of `U(χ)`, given the published identification of the
dynamic unipotent subgroup as a geometric unipotent radical. -/
theorem mem_range_radical_iff (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    {G P U : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {j : P ⟶ G} (hjc : IsClosedSubgroup j)
    (hj : (Dynamic.parabolic χ).IsRepresentedBy j) {r : U ⟶ P}
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ P.X) :
    x ∈ (SubgroupFunctor.range r).carrier T ↔
      x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Mono j.hom.hom := hj.1
  have hrep := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hle : SubgroupFunctor.range (Dynamic.Affine.unipotentHom χ) ≤ Dynamic.parabolic χ := by
    rw [hrep.2]
    exact Dynamic.unipotent_le_parabolic χ
  set r' := hj.factorHom (Dynamic.Affine.unipotentHom χ) hle with hr'def
  have hr'j : r' ≫ j = Dynamic.Affine.unipotentHom χ := hj.factorHom_comp _ hle
  have hr'c : IsClosedSubgroup r' := by
    apply IsClosedSubgroup.of_comp hjc
    rw [hr'j]
    exact Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have hr' : IsGeometricUnipotentRadical r' := by
    apply hGUR k G hG χ P _ j r' hj
    rw [hr'j]
    exact hrep
  have : IsClosedImmersion r'.hom.hom.left := hr'c
  have : Mono r'.hom.hom := Over.mono_of_mono_left _
  have hrange : SubgroupFunctor.range r = SubgroupFunctor.range r' := by
    apply le_antisymm
    · let b := toAlgebraicClosure k
      obtain ⟨hSurj, hFlat, hQC⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
      let : Surjective b := hSurj
      let : Flat b := hFlat
      let : QuasiCompact b := hQC
      apply SubgroupFunctor.le_range_of_baseChange_le b r'
      rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
      exact hr'.2.2.2.2.2.2.2.2 _ _ hr.2.isClosedSubgroup hr.2.smooth hr.2.connectedSpace
        hr.2.isUnipotent hr.2.isNormal
    · exact hr.1.greatest _ r' hr'c hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1
  rw [hrange, ← hrep.2, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← hr'j, Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (cancel_mono j.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hr'j, hy]

/-- **Reduction of rational Levi conjugacy to dynamic structure theory.** The published
statements that rational parabolics are dynamic parabolics and that the dynamic unipotent
subgroup is the geometric unipotent radical, together with the conjugacy of a cocharacter
to a cocharacter congruent to it modulo `U(χ)` by a rational point of `U(χ)`, imply
`RationalLeviConjugacyStatement`. -/
theorem rationalLeviConjugacy_of_dynamic
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    (hlift : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom G.X.hom] (χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
      ψ.hom.hom * (χ.hom.hom)⁻¹ ∈
          (Dynamic.unipotent χ).carrier (Gm (Spec (CommRingCat.of k))).X →
        ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ∧
            χ ≫ (G.innerIso u).hom = ψ) :
    RationalLeviConjugacyStatement.{u} := by
  intro k _ G hG P j hj L L' l l' hl hl' U r hr
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := hG.isSeparated
  have hjc : IsClosedSubgroup j := hj.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  have : Mono r.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  have : Mono l.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion l'.hom.hom.left := hl'.isClosedSubgroup
  have : Mono l'.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hjc).1 hj
  have hjP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨inferInstance, hχ⟩
  have hrU : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
      x ∈ (SubgroupFunctor.range r).carrier T ↔
        x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T :=
    fun _ x => mem_range_radical_iff hGUR hG χ hjc hjP hr x
  have leviData : ∀ {M : GroupScheme (Spec (CommRingCat.of k))} (m : M ⟶ P),
      IsRationalLeviSubgroup m → ∃ qm : P ⟶ M, m ≫ qm = 𝟙 M ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
          x ≫ qm.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T := by
    intro M m hm
    obtain ⟨U₀, r₀, qm, hr₀, -, hmq, hker⟩ := hm.exists_unipotentRadical_retraction
    refine ⟨qm, hmq, fun T x => ?_⟩
    rw [hker, hr₀.1.range_eq hr.1, hrU]
  obtain ⟨q₁, hlq₁, hker₁⟩ := leviData l hl
  obtain ⟨q₂, hlq₂, hker₂⟩ := leviData l' hl'
  obtain ⟨u₁, hu₁, hμ₁⟩ := hlift k G χ _
    (leviCocharacter_mul_inv_mem (hj := hjP) l q₁ hlq₁ hker₁)
  obtain ⟨u₂, hu₂, hμ₂⟩ := hlift k G χ _
    (leviCocharacter_mul_inv_mem (hj := hjP) l' q₂ hlq₂ hker₂)
  have hR₁ := range_comp_innerIso_inv_eq_centralizer l q₁ hlq₁ hker₁ hu₁ hμ₁
  have hR₂ := range_comp_innerIso_inv_eq_centralizer l' q₂ hlq₂ hker₂ hu₂ hμ₂
  have : IsIso (G.innerIso u₁).inv.hom.hom :=
    inferInstanceAs (IsIso ((Grp.forget _).map (G.innerIso u₁).inv))
  have : IsIso (G.innerIso u₂).inv.hom.hom :=
    inferInstanceAs (IsIso ((Grp.forget _).map (G.innerIso u₂).inv))
  have hrep₁ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ j ≫ (G.innerIso u₁).inv) :=
    ⟨by simp only [Grp.comp_hom_hom]; infer_instance, hR₁⟩
  have hrep₂ : (Dynamic.centralizer χ).IsRepresentedBy (l' ≫ j ≫ (G.innerIso u₂).inv) :=
    ⟨by simp only [Grp.comp_hom_hom]; infer_instance, hR₂⟩
  let e₀ := SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hrep₁ hrep₂
  have he₀ : e₀.hom ≫ l' ≫ j ≫ (G.innerIso u₂).inv = l ≫ j ≫ (G.innerIso u₁).inv :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hrep₁ hrep₂
  obtain ⟨v₁, hv₁⟩ := exists_comp_eq_of_mem_parabolic χ hjP
    (Dynamic.unipotent_le_parabolic χ _ hu₁)
  obtain ⟨v₂, hv₂⟩ := exists_comp_eq_of_mem_parabolic χ hjP
    (Dynamic.unipotent_le_parabolic χ _ hu₂)
  -- the conjugating point of the parabolic
  have hconj : l ≫ (P.innerIso (v₂ * v₁⁻¹)).hom = e₀.hom ≫ l' := by
    apply hjP.hom_ext
    rw [Category.assoc, innerIso_hom_comp j, MonObj.mul_comp, GrpObj.inv_comp, hv₁, hv₂,
      innerIso_mul_hom, innerIso_inv_hom, ← Category.assoc j, ← Category.assoc l, ← he₀]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hqmem : v₂ * v₁⁻¹ ∈ (SubgroupFunctor.range r).carrier _ := by
    rw [hrU, MonObj.mul_comp, GrpObj.inv_comp, hv₁, hv₂]
    exact mul_mem hu₂ (inv_mem hu₁)
  obtain ⟨q, hq⟩ := SubgroupFunctor.mem_range.mp hqmem
  refine ⟨q, ⟨e₀, by rw [hq]; exact hconj⟩, ?_⟩
  rintro q' ⟨e', he'⟩
  have hinv : l' ≫ (P.innerIso (q ≫ r.hom.hom)).inv = e₀.inv ≫ l := by
    rw [hq, Iso.eq_inv_comp, ← Category.assoc, ← hconj, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hg : l ≫ (P.innerIso ((q ≫ r.hom.hom)⁻¹ * (q' ≫ r.hom.hom))).hom =
      (e' ≪≫ e₀.symm).hom ≫ l := by
    rw [innerIso_mul_hom, innerIso_inv_hom, ← Category.assoc, he', Category.assoc, hinv]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hgU : ((q ≫ r.hom.hom)⁻¹ * (q' ≫ r.hom.hom)) ≫ j.hom.hom ∈
      (Dynamic.unipotent χ).carrier _ := by
    rw [← hrU, ← GrpObj.inv_comp, ← MonObj.mul_comp]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  have h1 := eq_one_of_comp_innerIso l q₁ hlq₁ hker₁ hu₁ hμ₁ hgU _ hg
  rw [inv_mul_eq_one] at h1
  exact ((cancel_mono r.hom.hom).mp h1).symm

end Field

end DynamicLeviConjugacy

end Langlands.GroupScheme
