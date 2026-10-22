import Langlands.Cohomology.Tate.ZeroProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- An auxiliary splice with zero connecting differential, used only for comparison. -/
def zeroSpliceConnectData (A : Rep.{u} R G) :
    CochainComplex.ConnectData (groupHomology.inhomogeneousChains A)
      (groupCohomology.inhomogeneousCochains A) where
  d₀ := 0
  comp_d₀ := by simp
  d₀_comp := by simp

/-- The auxiliary complex retains the actual ordinary chains and cochains. -/
abbrev zeroSpliceComplex (A : Rep.{u} R G) :=
  (zeroSpliceConnectData A).cochainComplex

def zeroSpliceMap {A B : Rep.{u} R G} (f : A ⟶ B) :
    zeroSpliceComplex A ⟶ zeroSpliceComplex B :=
  CochainComplex.ConnectData.map _ _
    (groupHomology.chainsMap (MonoidHom.id G) f)
    (groupCohomology.cochainsMap (MonoidHom.id G) f) (by simp [zeroSpliceConnectData])

/-- Coefficient functor for the comparison complex. -/
def zeroSpliceFunctor : Rep.{u} R G ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := zeroSpliceComplex
  map := zeroSpliceMap
  map_id _ := by simp [zeroSpliceMap]
  map_comp f g := by
    simp [zeroSpliceMap, CochainComplex.ConnectData.map_comp_map,
      ← groupHomology.chainsMap_comp]
    rfl

instance : (zeroSpliceFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero A B := by
    ext (i | i) : 1
    · change (groupCohomology.cochainsMap (MonoidHom.id G) (0 : A ⟶ B)).f i = 0
      simp
    · change (groupHomology.chainsMap (MonoidHom.id G) (0 : A ⟶ B)).f i = 0
      simp

lemma zeroSplice_shortExact {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) :
    (S.map zeroSpliceFunctor).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  rintro (_ | n)
  · exact groupCohomology.map_cochainsFunctor_eval_shortExact hS _
  · exact groupHomology.map_chainsFunctor_eval_shortExact hS n

variable [Fintype G] [Fintype H]

/-- Any ordinary cochain pullback extends from the zero splice to the actual Tate complex. -/
def cochainsToTate {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) :
    zeroSpliceComplex A ⟶ tateComplex B :=
  CochainComplex.ConnectData.map _ _ 0 (groupCohomology.cochainsMap f φ)
    (by simp [zeroSpliceConnectData])

omit [Fintype G] in
/-- On positive homology this comparison is exactly the ordinary cochain map. -/
lemma cochainsToTate_homology {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (cochainsToTate f φ) n =
      ((zeroSpliceConnectData A).homologyIsoPos n n rfl).hom ≫
        groupCohomology.map f φ n ≫
          ((TateCohomology.isoGroupCohomology n).app B).inv :=
  CochainComplex.ConnectData.homologyMap_map_of_eq_succ _ _ _ _ _ n _ rfl

omit [Fintype G] in
lemma cochainsToTate_naturality
    {A A' : Rep.{u} R G} {B B' : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) (ψ : Rep.res f A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B')
    (h : φ ≫ b = (Rep.resFunctor f).map a ≫ ψ) :
    cochainsToTate f φ ≫ tateComplex.map b =
      zeroSpliceMap a ≫ cochainsToTate f ψ := by
  ext i : 1
  cases i with
  | ofNat n =>
    change (groupCohomology.cochainsMap f φ).f n ≫
        (groupCohomology.cochainsMap (MonoidHom.id H) b).f n =
      (groupCohomology.cochainsMap (MonoidHom.id G) a).f n ≫
        (groupCohomology.cochainsMap f ψ).f n
    ext x y
    exact ConcreteCategory.congr_hom h (x (f ∘ y))
  | negSucc n =>
    change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    simp

/-- A map of coefficient sequences gives a map from their comparison and Tate complexes. -/
def cochainsToTateSequence {S : ShortComplex (Rep.{u} R G)}
    {T : ShortComplex (Rep.{u} R H)} (f : H →* G)
    (F : S.map (Rep.resFunctor f) ⟶ T) :
    S.map zeroSpliceFunctor ⟶ T.map (tateComplexFunctor R H) where
  τ₁ := cochainsToTate f F.τ₁
  τ₂ := cochainsToTate f F.τ₂
  τ₃ := cochainsToTate f F.τ₃
  comm₁₂ := cochainsToTate_naturality f F.τ₁ F.τ₂ S.f T.f F.comm₁₂
  comm₂₃ := cochainsToTate_naturality f F.τ₂ F.τ₃ S.g T.g F.comm₂₃

omit [Fintype G] in
/-- Naturality of actual connecting maps for the comparison. -/
lemma cochainsToTate_delta {S : ShortComplex (Rep.{u} R G)}
    {T : ShortComplex (Rep.{u} R H)} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : H →* G) (F : S.map (Rep.resFunctor f) ⟶ T) (n : ℤ) :
    (zeroSplice_shortExact hS).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap (cochainsToTate f F.τ₁) (n + 1) =
      HomologicalComplex.homologyMap (cochainsToTate f F.τ₃) n ≫
        TateCohomology.δ hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (cochainsToTateSequence f F) (zeroSplice_shortExact hS)
    (TateCohomology.map_tateComplexFunctor_shortExact hT) n (n + 1) rfl

abbrev zeroSpliceShortComplex (A : Rep.{u} R G) : ShortComplex (ModuleCat R) :=
  ShortComplex.mk (0 : ModuleCat.of R A ⟶ ModuleCat.of R A) (groupCohomology.d₀₁ A)
    zero_comp

def zeroSpliceShortComplexIso (A : Rep.{u} R G) :
    (zeroSpliceComplex A).sc 0 ≅ zeroSpliceShortComplex A := by
  refine (zeroSpliceComplex A).isoSc' (-1) 0 1 (by simp) (by simp) ≪≫ ?_
  exact ShortComplex.isoMk (groupHomology.chainsIso₀ A)
    (groupCohomology.cochainsIso₀ A) (groupCohomology.cochainsIso₁ A)
    (by simp [zeroSpliceComplex, zeroSpliceConnectData])
    (groupCohomology.comp_d₀₁_eq A)

/-- Degree-zero homology of the zero splice consists of actual invariant elements. -/
def zeroSpliceHomologyData (A : Rep.{u} R G) :
    (zeroSpliceShortComplex A).LeftHomologyData where
  K := ModuleCat.of R A.ρ.invariants
  H := ModuleCat.of R A.ρ.invariants
  i := ModuleCat.ofHom A.ρ.invariants.subtype
  π := 𝟙 _
  wi := groupCohomology.subtype_comp_d₀₁ A
  hi := (groupCohomology.shortComplexH0_exact A).fIsKernel
  wπ := by
    apply (cancel_mono (groupCohomology.shortComplexH0 A).f).mp
    simp only [zero_comp]
    exact (groupCohomology.shortComplexH0_exact A).fIsKernel.fac
      (KernelFork.ofι _ (zeroSpliceShortComplex A).zero) WalkingParallelPair.zero
  hπ := CokernelCofork.IsColimit.ofId _ (by
    apply (cancel_mono (groupCohomology.shortComplexH0 A).f).mp
    rw [zero_comp]
    exact (groupCohomology.shortComplexH0_exact A).fIsKernel.fac
      (KernelFork.ofι _ (zeroSpliceShortComplex A).zero) WalkingParallelPair.zero)

def zeroSpliceZeroEquiv (A : Rep.{u} R G) :
    (zeroSpliceComplex A).homology 0 ≅ ModuleCat.of R A.ρ.invariants :=
  ShortComplex.homologyMapIso (zeroSpliceShortComplexIso A) ≪≫
    (zeroSpliceHomologyData A).homologyIso

/-- Ordinary pullback on invariant representatives. -/
def cochainInvariantMap {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) :
    A.ρ.invariants →ₗ[R] B.ρ.invariants where
  toFun a := ⟨φ.hom a, fun g => by
    rw [← Rep.hom_comm_apply φ g]
    exact congrArg φ.hom (a.property (f g))⟩
  map_add' a b := Subtype.ext (map_add φ.hom (a : A) (b : A))
  map_smul' r a := Subtype.ext (map_smul φ.hom r (a : A))

omit [Fintype G] in
/-- Comparison at zero is precisely passage from invariants to their Tate classes. -/
lemma cochainsToTate_zero_hom {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) :
    (zeroSpliceZeroEquiv A).inv ≫ HomologicalComplex.homologyMap (cochainsToTate f φ) 0 =
      ModuleCat.ofHom (cochainInvariantMap f φ) ≫ ModuleCat.ofHom (zeroClass B) := by
  let ψ : zeroSpliceShortComplex A ⟶ zeroShortComplex B :=
    (zeroSpliceShortComplexIso A).inv ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) 0).map
        (cochainsToTate f φ) ≫ (zeroShortComplexIso B).hom
  let γ := ShortComplex.leftHomologyMapData ψ (zeroSpliceHomologyData A) (zeroHomologyData B)
  have hψ : ψ.τ₂ = φ.toModuleCatHom := by
    change (groupCohomology.cochainsIso₀ A).inv ≫
      (groupCohomology.cochainsMap f φ).f 0 ≫
        (groupCohomology.cochainsIso₀ B).hom = φ.toModuleCatHom
    rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]
    simp
  have hK : γ.φK = ModuleCat.ofHom (cochainInvariantMap f φ) := by
    apply (cancel_mono (zeroHomologyData B).i).mp
    rw [γ.commi, hψ]
    rfl
  have hmap : HomologicalComplex.homologyMap (cochainsToTate f φ) 0 =
      (zeroSpliceZeroEquiv A).hom ≫ γ.φH ≫ (zeroEquiv B).inv := by
    apply (cancel_mono (zeroEquiv B).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg
      (fun z => (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso A)).hom ≫ z)
      γ.homologyMap_comm
    simp only [ψ, ShortComplex.homologyMap_comp, Category.assoc] at hh
    change (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso A)).hom ≫
      (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso A)).inv ≫
      HomologicalComplex.homologyMap (cochainsToTate f φ) 0 ≫
      (ShortComplex.homologyMapIso (zeroShortComplexIso B)).hom ≫
      (zeroHomologyData B).homologyIso.hom =
      (ShortComplex.homologyMapIso (zeroSpliceShortComplexIso A)).hom ≫
      (zeroSpliceHomologyData A).homologyIso.hom ≫ γ.φH at hh
    simpa only [Iso.hom_inv_id_assoc, zeroSpliceZeroEquiv, zeroEquiv,
      Iso.trans_hom, Category.assoc] using hh
  have hπ : γ.φH =
      ModuleCat.ofHom (cochainInvariantMap f φ) ≫ ModuleCat.ofHom (normImage B).mkQ := by
    simpa only [hK, zeroSpliceHomologyData, zeroHomologyData, Category.id_comp] using γ.commπ
  rw [hmap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hπ]
  rfl

omit [Fintype G] in
lemma cochainsToTate_zero {A : Rep.{u} R G} {B : Rep.{u} R H}
    (f : H →* G) (φ : Rep.res f A ⟶ B) (a : A.ρ.invariants) :
    HomologicalComplex.homologyMap (cochainsToTate f φ) 0 ((zeroSpliceZeroEquiv A).inv a) =
      zeroClass B (cochainInvariantMap f φ a) :=
  ConcreteCategory.congr_hom (cochainsToTate_zero_hom f φ) a

lemma cochainsToTate_homology_id (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 A)) n =
      ((zeroSpliceConnectData A).homologyIsoPos n n rfl).hom ≫
        ((TateCohomology.isoGroupCohomology n).app A).inv := by
  refine (cochainsToTate_homology (MonoidHom.id G) (𝟙 A) n).trans ?_
  have hi : groupCohomology.map (MonoidHom.id G) (𝟙 A) n = 𝟙 _ :=
    groupCohomology.map_id n
  exact (congrArg (fun z : groupCohomology A n ⟶ groupCohomology A n =>
    ((zeroSpliceConnectData A).homologyIsoPos n n rfl).hom ≫ z ≫
      ((TateCohomology.isoGroupCohomology n).app A).inv) hi).trans
    (by rfl)

/-- Positive-degree comparison with the actual Tate groups, using the existing ordinary isomorphism. -/
def cochainsToTateIso (A : Rep.{u} R G) (n : ℕ) [NeZero n] :
    (zeroSpliceComplex A).homology n ≅ tateCohomology A n :=
  (zeroSpliceConnectData A).homologyIsoPos n n rfl ≪≫
    ((TateCohomology.isoGroupCohomology n).app A).symm

/-- The comparison to actual Tate cohomology is surjective in every nonnegative degree. -/
lemma cochainsToTate_surjective (A : Rep.{u} R G) (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (cochainsToTate (MonoidHom.id G) (𝟙 A)) n) := by
  cases n with
  | zero =>
    intro x
    obtain ⟨a, rfl⟩ := zeroClass_surjective A x
    exact ⟨(zeroSpliceZeroEquiv A).inv a, cochainsToTate_zero _ _ a⟩
  | succ n =>
    rw [cochainsToTate_homology_id]
    exact (cochainsToTateIso A (n + 1)).toLinearEquiv.surjective

end Langlands.Tate
