import Langlands.Cohomology.Tate.Reindex
import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G H : Type u} [CommRing R] [Group G] [Group H]
variable [Fintype G] [Fintype H]
variable (e : G ≃* H)
variable {A A' : Rep.{u} R G} {B B' : Rep.{u} R H}

/-- A coefficient square induces a square of actual Tate complexes. -/
lemma reindexComplex_naturality
    (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (ψ : Rep.res e.symm.toMonoidHom A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B')
    (h : φ ≫ g = (Rep.resFunctor e.symm.toMonoidHom).map f ≫ ψ) :
    reindexComplex e φ ≫ tateComplex.map g =
      tateComplex.map f ≫ reindexComplex e ψ := by
  ext i : 1
  cases i with
  | ofNat n =>
    change (groupCohomology.cochainsMap e.symm.toMonoidHom φ).f n ≫
        (groupCohomology.cochainsMap (MonoidHom.id H) g).f n =
      (groupCohomology.cochainsMap (MonoidHom.id G) f).f n ≫
        (groupCohomology.cochainsMap e.symm.toMonoidHom ψ).f n
    ext x y
    exact ConcreteCategory.congr_hom h (x (e.symm.toMonoidHom ∘ y))
  | negSucc n =>
    change (groupHomology.chainsMap e.toMonoidHom (reindexCoefficient e φ)).f n ≫
        (groupHomology.chainsMap (MonoidHom.id H) g).f n =
      (groupHomology.chainsMap (MonoidHom.id G) f).f n ≫
        (groupHomology.chainsMap e.toMonoidHom (reindexCoefficient e ψ)).f n
    ext x a y
    simpa [groupHomology.chainsMap_f,
      reindexCoefficient] using congrArg
        (fun b => Finsupp.single (e.toMonoidHom ∘ x) b y)
        (ConcreteCategory.congr_hom h a)

/-- The induced square on the existing Tate cohomology functors. -/
lemma reindex_naturality
    (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (ψ : Rep.res e.symm.toMonoidHom A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B')
    (h : φ ≫ g = (Rep.resFunctor e.symm.toMonoidHom).map f ≫ ψ) (n : ℤ) :
    reindex e φ n ≫ (tateCohomologyFunctor n).map g =
      (tateCohomologyFunctor n).map f ≫ reindex e ψ n := by
  change HomologicalComplex.homologyMap (reindexComplex e φ) n ≫
      HomologicalComplex.homologyMap (tateComplex.map g) n =
    HomologicalComplex.homologyMap (tateComplex.map f) n ≫
      HomologicalComplex.homologyMap (reindexComplex e ψ) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun z => HomologicalComplex.homologyMap z n)
    (reindexComplex_naturality e φ ψ f g h)

/-- Reindex all three terms of a short coefficient sequence on actual complexes. -/
def reindexShortComplexMap
    {S : ShortComplex (Rep.{u} R G)} {T : ShortComplex (Rep.{u} R H)}
    (F : S.map (Rep.resFunctor e.symm.toMonoidHom) ⟶ T) :
    S.map (tateComplexFunctor R G) ⟶ T.map (tateComplexFunctor R H) where
  τ₁ := reindexComplex e F.τ₁
  τ₂ := reindexComplex e F.τ₂
  τ₃ := reindexComplex e F.τ₃
  comm₁₂ := reindexComplex_naturality e F.τ₁ F.τ₂ S.f T.f F.comm₁₂
  comm₂₃ := reindexComplex_naturality e F.τ₂ F.τ₃ S.g T.g F.comm₂₃

/-- Reindexing commutes with the actual connecting homomorphisms. -/
lemma reindex_delta
    {S : ShortComplex (Rep.{u} R G)} {T : ShortComplex (Rep.{u} R H)}
    (hS : S.ShortExact) (hT : T.ShortExact)
    (F : S.map (Rep.resFunctor e.symm.toMonoidHom) ⟶ T) (n : ℤ) :
    TateCohomology.δ hS n ≫ reindex e F.τ₁ (n + 1) =
      reindex e F.τ₃ n ≫ TateCohomology.δ hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (reindexShortComplexMap e F)
    (TateCohomology.map_tateComplexFunctor_shortExact hS)
    (TateCohomology.map_tateComplexFunctor_shortExact hT) n (n + 1) rfl

/-- The underlying map on invariant elements for a change of group coordinates. -/
def reindexInvariants (φ : Rep.res e.symm.toMonoidHom A ⟶ B) :
    A.ρ.invariants →ₗ[R] B.ρ.invariants where
  toFun a := ⟨φ.hom a, fun h => by
    rw [← Rep.hom_comm_apply φ h]
    exact congrArg φ.hom (a.property (e.symm h))⟩
  map_add' a b := Subtype.ext (map_add φ.hom (a : A) (b : A))
  map_smul' r a := Subtype.ext (map_smul φ.hom r (a : A))

/-- In degree zero, actual complex reindexing sends an invariant to its image. -/
lemma reindex_zeroClass_hom (φ : Rep.res e.symm.toMonoidHom A ⟶ B) :
    ModuleCat.ofHom (zeroClass A) ≫ reindex e φ 0 =
      ModuleCat.ofHom (reindexInvariants e φ) ≫ ModuleCat.ofHom (zeroClass B) := by
  let ψ : zeroShortComplex A ⟶ zeroShortComplex B :=
    (zeroShortComplexIso A).inv ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).map
        (reindexComplex e φ) ≫ (zeroShortComplexIso B).hom
  let γ := ShortComplex.leftHomologyMapData ψ (zeroHomologyData A) (zeroHomologyData B)
  have hψ : ψ.τ₂ = φ.toModuleCatHom := by
    change (groupCohomology.cochainsIso₀ A).inv ≫
      (groupCohomology.cochainsMap e.symm.toMonoidHom φ).f 0 ≫
        (groupCohomology.cochainsIso₀ B).hom = φ.toModuleCatHom
    rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]
    simp
  have hK : γ.φK = ModuleCat.ofHom (reindexInvariants e φ) := by
    apply (cancel_mono (zeroHomologyData B).i).mp
    rw [γ.commi, hψ]
    rfl
  have hmap : reindex e φ 0 =
      (zeroEquiv A).hom ≫ γ.φH ≫ (zeroEquiv B).inv := by
    apply (cancel_mono (zeroEquiv B).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg
      (fun z => (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫ z)
      γ.homologyMap_comm
    simp only [ψ, ShortComplex.homologyMap_comp, Category.assoc] at hh
    change (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso A)).inv ≫
      reindex e φ 0 ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso B)).hom ≫
      (zeroHomologyData B).homologyIso.hom =
      (ShortComplex.homologyMapIso (zeroShortComplexIso A)).hom ≫
      (zeroHomologyData A).homologyIso.hom ≫ γ.φH at hh
    simpa only [Iso.hom_inv_id_assoc, zeroEquiv, Iso.trans_hom, Category.assoc] using hh
  have hπ : ModuleCat.ofHom (normImage A).mkQ ≫ γ.φH =
      ModuleCat.ofHom (reindexInvariants e φ) ≫ ModuleCat.ofHom (normImage B).mkQ := by
    simpa only [hK, zeroHomologyData] using γ.commπ
  change (ModuleCat.ofHom (normImage A).mkQ ≫ (zeroEquiv A).inv) ≫ reindex e φ 0 =
      ModuleCat.ofHom (reindexInvariants e φ) ≫
        (ModuleCat.ofHom (normImage B).mkQ ≫ (zeroEquiv B).inv)
  rw [hmap]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun z => z ≫ (zeroEquiv B).inv) hπ

lemma reindex_zeroClass (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (a : A.ρ.invariants) :
    reindex e φ 0 (zeroClass A a) = zeroClass B (reindexInvariants e φ a) :=
  ConcreteCategory.congr_hom (reindex_zeroClass_hom e φ) a

end Langlands.Tate
