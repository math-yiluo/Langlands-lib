import Langlands.Cohomology.Tate.CochainComparison
import Langlands.Cohomology.Tate.SpliceRepresentatives

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- Actual homology maps carry the class of a cycle to the class of its image. -/
lemma homologyMap_cycleClass {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (n : ℤ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    HomologicalComplex.homologyMap f n (cycleClass K n x hx) =
      cycleClass L n (f.f n x) (by
        rw [← complexMap_d_apply, hx, map_zero]) := by
  refine (ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n)
    (K.cyclesMk x (n + 1) (by simp) hx)).trans ?_
  apply congrArg (L.homologyπ n)
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  calc
    _ = f.f n (K.iCycles n (K.cyclesMk x (n + 1) (by simp) hx)) :=
      ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) _
    _ = f.f n x := congrArg (f.f n) (K.i_cyclesMk _ _ _ _)
    _ = _ := (L.i_cyclesMk _ _ _ _).symm

variable [Fintype G] [Fintype H]

/-- The ordinary chain pushforward extends from the actual Tate complex to the zero splice. -/
def tateToChains {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : G →* H) (φ : A ⟶ Rep.res f B) :
    tateComplex A ⟶ zeroSpliceComplex B :=
  CochainComplex.ConnectData.map _ _ (groupHomology.chainsMap f φ) 0
    (by simp [zeroSpliceConnectData])

omit [Fintype H] in
/-- Away from the splice, the homology map is exactly Mathlib's ordinary chain pushforward. -/
lemma tateToChains_homology {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : G →* H) (φ : A ⟶ Rep.res f B) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (tateToChains f φ) (-(n + 1 : ℤ)) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        groupHomology.map f φ n ≫
          ((zeroSpliceConnectData B).homologyIsoNeg n (-(n + 1 : ℤ)) rfl).inv :=
  CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ _ _ _ _ _ n _ rfl

omit [Fintype H] in
lemma tateToChains_naturality
    {A A' : Rep.{u} R G} {B B' : Rep.{u} R H}
    (f : G →* H) (φ : A ⟶ Rep.res f B) (ψ : A' ⟶ Rep.res f B')
    (a : A ⟶ A') (b : B ⟶ B')
    (h : φ ≫ (Rep.resFunctor f).map b = a ≫ ψ) :
    tateToChains f φ ≫ zeroSpliceMap b =
      tateComplex.map a ≫ tateToChains f ψ := by
  ext i : 1
  cases i with
  | ofNat n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    simp
  | negSucc n =>
    change (groupHomology.chainsMap f φ).f n ≫
        (groupHomology.chainsMap (MonoidHom.id H) b).f n =
      (groupHomology.chainsMap (MonoidHom.id G) a).f n ≫
        (groupHomology.chainsMap f ψ).f n
    ext x c y
    simpa [groupHomology.chainsMap_f] using congrArg
      (fun d => Finsupp.single (f ∘ x) d y) (ConcreteCategory.congr_hom h c)

/-- Comparison of entire short exact coefficient sequences on the actual complexes. -/
def tateToChainsSequence {S : ShortComplex (Rep.{u} R G)}
    {T : ShortComplex (Rep.{u} R H)} (f : G →* H)
    (F : S ⟶ T.map (Rep.resFunctor f)) :
    S.map (tateComplexFunctor R G) ⟶ T.map zeroSpliceFunctor where
  τ₁ := tateToChains f F.τ₁
  τ₂ := tateToChains f F.τ₂
  τ₃ := tateToChains f F.τ₃
  comm₁₂ := tateToChains_naturality f F.τ₁ F.τ₂ S.f T.f F.comm₁₂
  comm₂₃ := tateToChains_naturality f F.τ₂ F.τ₃ S.g T.g F.comm₂₃

omit [Fintype H] in
/-- Naturality for the actual connecting maps, including the negative splice transition. -/
lemma tateToChains_delta {S : ShortComplex (Rep.{u} R G)}
    {T : ShortComplex (Rep.{u} R H)} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : G →* H) (F : S ⟶ T.map (Rep.resFunctor f)) (n : ℤ) :
    TateCohomology.δ hS n ≫
        HomologicalComplex.homologyMap (tateToChains f F.τ₁) (n + 1) =
      HomologicalComplex.homologyMap (tateToChains f F.τ₃) n ≫
        (zeroSplice_shortExact hT).δ n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (tateToChainsSequence f F) (TateCohomology.map_tateComplexFunctor_shortExact hS)
    (zeroSplice_shortExact hT) n (n + 1) rfl

/-- In degree minus one every coefficient vector is a cycle in the auxiliary zero splice. -/
def zeroSpliceMinusOneClass (A : Rep.{u} R G) (a : A) :
    (zeroSpliceComplex A).homology (-1) :=
  cycleClass (zeroSpliceComplex A) (-1) ((groupHomology.chainsIso₀ A).inv a)
    (by
      change (0 : (zeroSpliceComplex A).X (-1) ⟶ (zeroSpliceComplex A).X 0)
        ((groupHomology.chainsIso₀ A).inv a) = 0
      rfl)

omit [Fintype H] in
/-- The comparison sends a norm-zero representative to its ordinary zero-chain class. -/
lemma tateToChains_minusOne {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : G →* H) (φ : A ⟶ Rep.res f B) (a : A) (ha : A.ρ.norm a = 0) :
    HomologicalComplex.homologyMap (tateToChains f φ) (-1) (minusOneClass A a ha) =
      zeroSpliceMinusOneClass B (φ.hom a) := by
  rw [minusOneClass, homologyMap_cycleClass]
  have hrep : (tateToChains f φ).f (-1) ((groupHomology.chainsIso₀ A).inv a) =
      (groupHomology.chainsIso₀ B).inv (φ.hom a) := by
    apply (groupHomology.chainsIso₀ B).toLinearEquiv.injective
    change (groupHomology.chainsIso₀ B).hom
      ((groupHomology.chainsMap f φ).f 0 ((groupHomology.chainsIso₀ A).inv a)) =
      (groupHomology.chainsIso₀ B).hom ((groupHomology.chainsIso₀ B).inv (φ.hom a))
    rw [Iso.inv_hom_id_apply]
    have hh :=
      ConcreteCategory.congr_hom
        (groupHomology.chainsMap_f_0_comp_chainsIso₀ f φ) ((groupHomology.chainsIso₀ A).inv a)
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hh
    exact hh
  dsimp only [zeroSpliceMinusOneClass]
  congr 1

lemma tateToChains_homology_id (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (tateToChains (MonoidHom.id G) (𝟙 A)) (-(n + 1 : ℤ)) =
      ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫
        ((zeroSpliceConnectData A).homologyIsoNeg n (-(n + 1 : ℤ)) rfl).inv := by
  rw [tateToChains_homology]
  have hi : groupHomology.map (MonoidHom.id G) (𝟙 A) n = 𝟙 _ := groupHomology.map_id n
  exact (congrArg (fun z : groupHomology A n ⟶ groupHomology A n =>
    ((TateCohomology.isoGroupHomology (-(n + 1 : ℤ)) n rfl).app A).hom ≫ z ≫
      ((zeroSpliceConnectData A).homologyIsoNeg n (-(n + 1 : ℤ)) rfl).inv) hi).trans
    (by rfl)

end Langlands.Tate
