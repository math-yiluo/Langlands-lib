import Langlands.GroupScheme.Dynamic.LeviParabolicDefinitions
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # Combinations of commuting cocharacters and extension from a Levi -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G L : GroupScheme S}

/-- Points in the dynamic centralizer commute with every value of the cocharacter. -/
theorem commute_cocharacter_of_mem_centralizer
    (χ : (Gm S).toGrp ⟶ G) {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (centralizer χ).carrier T) (t : T ⟶ (Gm S).X) :
    Commute g (t ≫ χ.hom.hom) := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer] at hg
  simpa only [Category.id_comp] using hg T (𝟙 T) t

/-- The pointwise product of two cocharacters with commuting images. -/
def commutingProduct (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ) : (Gm S).toGrp ⟶ G :=
  homOfPoints (fun T =>
    { toFun := fun t => (t ≫ χ.hom.hom) * (t ≫ tau.hom.hom)
      map_one' := by simp only [MonObj.one_comp, mul_one]
      map_mul' := fun t s => by
        simp only [MonObj.mul_comp]
        exact (commute_cocharacter_of_mem_centralizer χ
          (htau T (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)) s).symm.mul_mul_mul_comm _ _ })
    (by
      intro T T' a t
      change (a ≫ t) ≫ χ.hom.hom * (a ≫ t) ≫ tau.hom.hom =
        a ≫ (t ≫ χ.hom.hom * t ≫ tau.hom.hom)
      simp only [Category.assoc, MonObj.comp_mul])

@[simp] theorem comp_commutingProduct
    (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ)
    {T : Over S} (t : T ⟶ (Gm S).X) :
    t ≫ (commutingProduct χ tau htau).hom.hom =
      (t ≫ χ.hom.hom) * (t ≫ tau.hom.hom) :=
by
  unfold commutingProduct
  rw [comp_homOfPoints]
  · rfl
  · intro T T' a t
    change (a ≫ t) ≫ χ.hom.hom * (a ≫ t) ≫ tau.hom.hom =
      a ≫ (t ≫ χ.hom.hom * t ≫ tau.hom.hom)
    simp only [Category.assoc, MonObj.comp_mul]

/-- Multiplying by a commuting cocharacter does not change the orbit of a point
fixed by that cocharacter. -/
theorem orbit_commutingProduct_of_mem_centralizer
    (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ)
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (centralizer χ).carrier T) :
    orbit (commutingProduct χ tau htau) g = orbit tau g := by
  let a := snd T (Gm S).X ≫ χ.hom.hom
  let b := snd T (Gm S).X ≫ tau.hom.hom
  let x := fst T (Gm S).X ≫ g
  have hb : Commute b a := commute_cocharacter_of_mem_centralizer χ
    (htau _ (SubgroupFunctor.mem_range.mpr ⟨snd T (Gm S).X, rfl⟩)) _
  have hx : Commute x a := commute_cocharacter_of_mem_centralizer χ
    ((centralizer χ).comp_mem (fst T (Gm S).X) hg) _
  change (snd T (Gm S).X ≫ (commutingProduct χ tau htau).hom.hom) * x *
      (snd T (Gm S).X ≫ (commutingProduct χ tau htau).hom.hom)⁻¹ = b * x * b⁻¹
  rw [comp_commutingProduct]
  change (a * b) * x * (a * b)⁻¹ = b * x * b⁻¹
  calc
    _ = a * (b * x * b⁻¹) * a⁻¹ := by group
    _ = (b * x * b⁻¹) * a * a⁻¹ := by
      rw [((hb.mul_left hx).mul_left hb.inv_left).symm.eq]
    _ = _ := mul_inv_cancel_right _ _

/-- The centralizer of a cocharacter also centralizes its precomposition. -/
theorem centralizer_le_precomp (χ : (Gm S).toGrp ⟶ G)
    (rho : (Gm S).toGrp ⟶ (Gm S).toGrp) :
    centralizer χ ≤ centralizer (rho ≫ χ) := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer χ]
  exact torusCentralizer_le_dynamicCentralizer χ rho

/-- The ambient combination `χ(t^n) tau(t)` for cocharacters with commuting images. -/
def cocharacterCombination (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ) (n : ℤ) :
    (Gm S).toGrp ⟶ G :=
  commutingProduct (CommGroupScheme.groupHom (Gm.powerHom S n) ≫ χ) tau
    (htau.trans (centralizer_le_precomp χ _))

@[simp] theorem comp_cocharacterCombination
    (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ) (n : ℤ)
    {T : Over S} (t : T ⟶ (Gm S).X) :
    t ≫ (cocharacterCombination χ tau htau n).hom.hom =
      ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom) := by
  rw [cocharacterCombination, comp_commutingProduct, Grp.comp_hom_hom,
    ← Category.assoc, Gm.powerHom_apply, Gm.comp_zsmul_id]

/-- On the original centralizer the combined cocharacter acts exactly as the
second cocharacter, for every integer coefficient. -/
theorem orbit_cocharacterCombination_of_mem_centralizer
    (χ tau : (Gm S).toGrp ⟶ G)
    (htau : SubgroupFunctor.range tau ≤ centralizer χ) (n : ℤ)
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (centralizer χ).carrier T) :
    orbit (cocharacterCombination χ tau htau n) g = orbit tau g :=
  orbit_commutingProduct_of_mem_centralizer _ _ _
    (centralizer_le_precomp χ _ _ hg)

/-- Any cocharacter of a represented centralizer has centralizing ambient image. -/
theorem range_comp_le_centralizer (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j) (ν : (Gm S).toGrp ⟶ L) :
    SubgroupFunctor.range (ν ≫ j) ≤ centralizer χ := by
  intro T x hx
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [← hj.2]
  exact SubgroupFunctor.mem_range.mpr ⟨t ≫ ν.hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

section Reduction

variable (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j)
    (ν : (Gm S).toGrp ⟶ L) (ψ : (Gm S).toGrp ⟶ G)
    (hOrbit : ∀ (T : Over S) (l : T ⟶ L.X),
      orbit ψ (l ≫ j.hom.hom) = orbit (ν ≫ j) (l ≫ j.hom.hom))

include hOrbit

/-- Identical restricted orbits give identical parabolic preimages. -/
theorem parabolic_comap_eq_of_orbit (hjc : IsClosedSubgroup j) :
    (parabolic ψ).comap j = parabolic ν := by
  rw [parabolic_eq_comap_of_isClosedSubgroup ν j hjc]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro l
  change (∃ e, IsOrbitExtension ψ (l ≫ j.hom.hom) e) ↔
    ∃ e, IsOrbitExtension (ν ≫ j) (l ≫ j.hom.hom) e
  simp only [IsOrbitExtension, hOrbit]

/-- Identical restricted orbits give identical identity-limit preimages. -/
theorem unipotent_comap_eq_of_orbit (hjc : IsClosedSubgroup j) :
    (unipotent ψ).comap j = unipotent ν := by
  rw [unipotent_eq_comap_of_isClosedSubgroup ν j hjc]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro l
  change HasLimit ψ (l ≫ j.hom.hom) 1 ↔ HasLimit (ν ≫ j) (l ≫ j.hom.hom) 1
  simp only [HasLimit, IsOrbitExtension, hOrbit]

/-- Identical restricted orbits give identical centralizer preimages. -/
theorem centralizer_comap_eq_of_orbit (hjc : IsClosedSubgroup j) :
    (centralizer ψ).comap j = centralizer ν := by
  rw [centralizer_eq_comap_of_isClosedSubgroup ν j hjc]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro l
  change (l ≫ j.hom.hom ∈ (centralizer ψ).carrier T) ↔
    (l ≫ j.hom.hom ∈ (centralizer (ν ≫ j)).carrier T)
  rw [mem_centralizer, mem_centralizer, hOrbit]

variable [IsSeparated G.X.hom]

/-- The exact two-factor formulas follow from three ambient inclusions and the
unchanged action on the represented centralizer. -/
theorem realization_of_inclusions (hjc : IsClosedSubgroup j)
    (hP : parabolic ψ ≤ parabolic χ)
    (hU : unipotent χ ≤ unipotent ψ)
    (hZ : centralizer ψ ≤ centralizer χ) :
    parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
      centralizer ψ = (centralizer ν).map j ∧
      unipotent ψ = extendFromCentralizer χ j hj (unipotent ν) := by
  have hPj := parabolic_comap_eq_of_orbit j ν ψ hOrbit hjc
  have hUj := unipotent_comap_eq_of_orbit j ν ψ hOrbit hjc
  have hZj := centralizer_comap_eq_of_orbit j ν ψ hOrbit hjc
  have hzfactor : ∀ (T : Over S) (g : T ⟶ G.X),
      g ∈ (parabolic χ).carrier T →
      ∃ l : T ⟶ L.X, ∃ n ∈ (unipotent χ).carrier T,
        (l ≫ j.hom.hom) * n = g := by
    intro T g hg
    let z := limit χ ⟨g, hg⟩
    have hz : z ∈ (centralizer χ).carrier T := limit_mem_centralizer χ _
    have hn : z⁻¹ * g ∈ (unipotent χ).carrier T := by
      have hh := ((hasLimit_of_mem_centralizer χ hz).inv χ).mul χ
        (hasLimit_limit χ ⟨g, hg⟩)
      change HasLimit χ (z⁻¹ * g) 1
      change HasLimit χ (z⁻¹ * g) (z⁻¹ * z) at hh
      simpa only [inv_mul_cancel] using hh
    rw [← hj.2] at hz
    obtain ⟨l, hl⟩ := SubgroupFunctor.mem_range.mp hz
    exact ⟨l, z⁻¹ * g, hn, by rw [hl, mul_inv_cancel_left]⟩
  have hprod : ∀ (F : SubgroupFunctor L) (E : SubgroupFunctor G),
      E ≤ parabolic χ → unipotent χ ≤ E → E.comap j = F →
      E = extendFromCentralizer χ j hj F := by
    intro F E hE hN hEj
    apply le_antisymm
    · intro T g hg
      obtain ⟨l, n, hn, heq⟩ := hzfactor T g (hE T hg)
      have hl : l ≫ j.hom.hom ∈ E.carrier T := by
        have hh := (E.carrier T).mul_mem hg ((E.carrier T).inv_mem (hN T hn))
        rwa [← heq, mul_inv_cancel_right] at hh
      rw [mem_extendFromCentralizer]
      exact ⟨l, by rw [← hEj]; exact hl, n, hn, heq⟩
    · intro T g hg
      obtain ⟨l, hl, n, hn, rfl⟩ := (mem_extendFromCentralizer χ j hj F T g).mp hg
      have hl' : l ∈ (E.comap j).carrier T := by rwa [hEj]
      exact (E.carrier T).mul_mem hl' (hN T hn)
  refine ⟨hprod _ _ hP (hU.trans (unipotent_le_parabolic ψ)) hPj, ?_,
    hprod _ _ ((unipotent_le_parabolic ψ).trans hP) hU hUj⟩
  apply le_antisymm
  · intro T g hg
    have hz := hZ T hg
    rw [← hj.2] at hz
    obtain ⟨l, rfl⟩ := SubgroupFunctor.mem_range.mp hz
    exact ⟨l, by rw [← hZj]; exact hg, rfl⟩
  · rintro T g ⟨l, hl, rfl⟩
    have hl' : l ∈ ((centralizer ψ).comap j).carrier T := by rwa [hZj]
    exact hl'

end Reduction

/-- For a cocharacter of the represented Levi, the three dominant inclusions
suffice for all three exact realization identities. -/
theorem realization_cocharacterCombination_of_inclusions
    (χ : (Gm S).toGrp ⟶ G) (j : L ⟶ G)
    (hj : (centralizer χ).IsRepresentedBy j) (hjc : IsClosedSubgroup j)
    (ν : (Gm S).toGrp ⟶ L) (n : ℤ) [IsSeparated G.X.hom] :
    let ψ := cocharacterCombination χ (ν ≫ j) (range_comp_le_centralizer χ j hj ν) n
    parabolic ψ ≤ parabolic χ →
      unipotent χ ≤ unipotent ψ →
      centralizer ψ ≤ centralizer χ →
      parabolic ψ = extendFromCentralizer χ j hj (parabolic ν) ∧
        centralizer ψ = (centralizer ν).map j ∧
        unipotent ψ = extendFromCentralizer χ j hj (unipotent ν) := by
  let ψ := cocharacterCombination χ (ν ≫ j) (range_comp_le_centralizer χ j hj ν) n
  dsimp only
  intro hP hU hZ
  apply realization_of_inclusions χ j hj ν ψ ?_ hjc hP hU hZ
  intro T l
  apply orbit_cocharacterCombination_of_mem_centralizer
  rw [← hj.2]
  exact SubgroupFunctor.mem_range.mpr ⟨l, rfl⟩

end Langlands.GroupScheme.Dynamic
