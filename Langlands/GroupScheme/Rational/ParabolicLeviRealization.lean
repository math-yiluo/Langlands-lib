import Langlands.GroupScheme.Rational.DynamicLeviConjugacyReduction
import Langlands.GroupScheme.Dynamic.UnipotentCocharacterConjugacy

/-! # One cocharacter realizing a rational parabolic and a rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicLeviConjugacy

section Base

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- If the range of `f ≫ e⁻¹` is the preimage of `F` under an isomorphism `e`, then the range
of `f` is `F`. -/
theorem range_eq_of_range_comp_inv_eq (f : H ⟶ G) (e : G ≅ G) (F : SubgroupFunctor G)
    (h : SubgroupFunctor.range (f ≫ e.inv) = F.comap e.hom) :
    SubgroupFunctor.range f = F := by
  have he : ∀ {T : Over S} (x : T ⟶ G.X), (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x := by
    intro T x
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ (f ≫ e.inv).hom.hom ∈ (F.comap e.hom).carrier T := by
      rw [← h]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    rw [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, ← Category.assoc, he] at hy
    exact hy
  · have hx' : x ≫ e.inv.hom.hom ∈ (F.comap e.hom).carrier T := by
      rw [SubgroupFunctor.mem_comap, he]
      exact hx
    rw [← h] at hx'
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx'
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    rw [← he x, ← hy, Grp.comp_hom_hom, ← Category.assoc, he]

/-- Conjugating a cocharacter by a base point of its dynamic parabolic does not change the
dynamic parabolic. -/
theorem parabolic_comp_innerIso_eq (χ : (Gm S).toGrp ⟶ G) {u : Over.mk (𝟙 S) ⟶ G.X}
    (hu : u ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 S))) :
    Dynamic.parabolic (χ ≫ (G.innerIso u).hom) = Dynamic.parabolic χ := by
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
  set c := G.constantPoint u T with hcdef
  have hc : c ∈ (Dynamic.parabolic χ).carrier T := (Dynamic.parabolic χ).comp_mem _ hu
  have key : ∀ y : T ⟶ G.X, y ∈ (Dynamic.parabolic χ).carrier T ↔
      c * y * c⁻¹ ∈ (Dynamic.parabolic (χ ≫ (G.innerIso u).hom)).carrier T := by
    intro y
    rw [hcdef, ← comp_innerIso_hom, ← SubgroupFunctor.mem_comap,
      ← Dynamic.parabolic_eq_comap_of_iso]
  have hx : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
  constructor
  · intro h
    have h' := (key (c⁻¹ * x * c)).2 (by rwa [hx])
    have h'' := mul_mem (mul_mem hc h') (inv_mem hc)
    rwa [hx] at h''
  · intro h
    have h' := (key (c⁻¹ * x * c)).1 (mul_mem (mul_mem (inv_mem hc) h) hc)
    rwa [hx] at h'

end Base

section Field

variable {k : Type u} [Field k]

/-- **One cocharacter for a parabolic and a Levi.** Given that rational parabolics are dynamic
parabolics and that the dynamic unipotent subgroup is the geometric unipotent radical, a
rational parabolic `j : P ⟶ G` of a connected reductive group and a rational Levi `l : L ⟶ P`
of it are the dynamic parabolic and the dynamic centralizer of a single cocharacter. -/
theorem exists_cocharacter_parabolic_levi
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    {G P L : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {j : P ⟶ G} (hj : IsParabolicSubgroup j) {l : L ⟶ P} (hl : IsRationalLeviSubgroup l) :
    ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      SubgroupFunctor.range j = Dynamic.parabolic ψ ∧
        SubgroupFunctor.range (l ≫ j) = Dynamic.centralizer ψ := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := hG.isSeparated
  have hjc : IsClosedSubgroup j := hj.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hjc).1 hj
  have hjP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨inferInstance, hχ⟩
  obtain ⟨U, r, q, hr, -, hlq, hker⟩ := hl.exists_unipotentRadical_retraction
  have hker' : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ P.X),
      x ≫ q.hom.hom = 1 ↔ x ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier T :=
    fun T x => by rw [hker, mem_range_radical_iff hGUR hG χ hjc hjP hr x]
  obtain ⟨v, hv, hμ⟩ := Dynamic.exists_unipotent_conj_of_mul_inv_mem χ _
    (leviCocharacter_mul_inv_mem (hj := hjP) l q hlq hker')
  have hR := range_comp_innerIso_inv_eq_centralizer l q hlq hker' hv hμ
  refine ⟨χ ≫ (G.innerIso v).hom, ?_, ?_⟩
  · rw [parabolic_comp_innerIso_eq χ (Dynamic.unipotent_le_parabolic χ _ hv), hχ]
  · refine range_eq_of_range_comp_inv_eq (l ≫ j) (G.innerIso v) _ ?_
    rw [Category.assoc, hR, Dynamic.centralizer_eq_comap_of_iso χ (G.innerIso v)]

/-- A chosen cocharacter realizing the supplied parabolic and Levi, under the
two explicit dynamic structure statements. -/
def parabolicLeviRealizingCocharacter
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    {G P L : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {j : P ⟶ G} (hj : IsParabolicSubgroup j) {l : L ⟶ P} (hl : IsRationalLeviSubgroup l) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  Classical.choose (exists_cocharacter_parabolic_levi hPD hGUR hG hj hl)

/-- Both original subgroup images are realized by the same chosen cocharacter. -/
theorem parabolicLeviRealizingCocharacter_spec
    (hPD : ParabolicDynamicStatement.{u})
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    {G P L : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {j : P ⟶ G} (hj : IsParabolicSubgroup j) {l : L ⟶ P} (hl : IsRationalLeviSubgroup l) :
    SubgroupFunctor.range j =
        Dynamic.parabolic (parabolicLeviRealizingCocharacter hPD hGUR hG hj hl) ∧
      SubgroupFunctor.range (l ≫ j) =
        Dynamic.centralizer (parabolicLeviRealizingCocharacter hPD hGUR hG hj hl) :=
  Classical.choose_spec (exists_cocharacter_parabolic_levi hPD hGUR hG hj hl)

end Field

end DynamicLeviConjugacy

end Langlands.GroupScheme
