import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.ZExtension
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.Reductive.CentralQuotientReductiveProof
import Langlands.GroupScheme.Reductive.DirectProductProof
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.Rational.CentralQuotientCenter
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Derived.EpiProductDetection
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof

/-! # Pushing a central cover out along a homomorphism into an induced torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace ZExtensionPushout

section General

variable {S : Scheme.{u}}

/-- A homomorphism with trivial kernel on every test scheme is a monomorphism. -/
theorem mono_of_comp_eq_one {A B : GroupScheme S} (f : A ⟶ B)
    (h : ∀ (T : Over S) (x : T ⟶ A.X), x ≫ f.hom.hom = 1 → x = 1) : Mono f.hom.hom := by
  constructor
  intro T x y hxy
  have e : (x * y⁻¹) ≫ f.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
  exact mul_inv_eq_one.mp (h T _ e)

/-- The kernel inclusion composed with the homomorphism is trivial. -/
theorem kernelι_comp_eq_one {A B : GroupScheme S} (f : A ⟶ B) :
    (kernelι f).hom.hom ≫ f.hom.hom = 1 :=
  (mem_range_kernelι_iff f _).mp (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)

variable (A B : GroupScheme S)

@[reassoc]
theorem prodInl_hom_fst : (prodInl A B).hom.hom ≫ fst A.X B.X = 𝟙 A.X := by
  have h := comp_homOfPoints (inlPoints A B) (inlPoints_naturality A B) A.X (𝟙 A.X)
  rw [Category.id_comp] at h
  change (prodInl A B).hom.hom = _ at h
  rw [h]
  exact congrArg Prod.fst ((productPointsEquiv A B A.X).apply_symm_apply (𝟙 A.X, 1))

@[reassoc]
theorem prodInl_hom_snd : (prodInl A B).hom.hom ≫ snd A.X B.X = 1 := by
  have h := comp_homOfPoints (inlPoints A B) (inlPoints_naturality A B) A.X (𝟙 A.X)
  rw [Category.id_comp] at h
  change (prodInl A B).hom.hom = _ at h
  rw [h]
  exact congrArg Prod.snd ((productPointsEquiv A B A.X).apply_symm_apply (𝟙 A.X, 1))

@[reassoc]
theorem prodInr_hom_fst : (prodInr A B).hom.hom ≫ fst A.X B.X = 1 := by
  have h := comp_homOfPoints (inrPoints A B) (inrPoints_naturality A B) B.X (𝟙 B.X)
  rw [Category.id_comp] at h
  change (prodInr A B).hom.hom = _ at h
  rw [h]
  exact congrArg Prod.fst ((productPointsEquiv A B B.X).apply_symm_apply (1, 𝟙 B.X))

@[reassoc]
theorem prodInr_hom_snd : (prodInr A B).hom.hom ≫ snd A.X B.X = 𝟙 B.X := by
  have h := comp_homOfPoints (inrPoints A B) (inrPoints_naturality A B) B.X (𝟙 B.X)
  rw [Category.id_comp] at h
  change (prodInr A B).hom.hom = _ at h
  rw [h]
  exact congrArg Prod.snd ((productPointsEquiv A B B.X).apply_symm_apply (1, 𝟙 B.X))

/-- The inclusion of a commutative second factor is central. -/
theorem isCentral_prodInr (Z : CommGroupScheme S) : IsCentral (prodInr A Z.toGrp) := by
  intro T x T' a w
  show _ * _ = _ * _
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, prodInr_hom_fst,
      MonObj.comp_one, MonObj.comp_one, one_mul, mul_one]
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact mul_comm _ _

/-- `prodInl` is a monomorphism. -/
instance mono_prodInl : Mono (prodInl A B).hom.hom :=
  mono_of_mono_fac (prodInl_hom_fst A B)

/-- `prodInr` is a monomorphism. -/
instance mono_prodInr : Mono (prodInr A B).hom.hom :=
  mono_of_mono_fac (prodInr_hom_snd A B)

end General

section Embedding

variable {k : Type u} [Field k] {G A₀ : GroupScheme (Spec (CommRingCat.of k))}
  {Z : CommGroupScheme (Spec (CommRingCat.of k))} (m : A₀ ⟶ G) (j : kernel m ⟶ Z.toGrp)

/-- The embedding `y ↦ (y, j y)` of the kernel of `m` into `A₀ × Z`. -/
abbrev embedding : kernel m ⟶ A₀ ⊗ Z.toGrp := lift (kernelι m) j

@[reassoc]
theorem embedding_hom_fst : (embedding m j).hom.hom ≫ fst A₀.X Z.X = (kernelι m).hom.hom := by
  change lift (kernelι m).hom.hom j.hom.hom ≫ fst A₀.X Z.X = _
  rw [lift_fst]

@[reassoc]
theorem embedding_hom_snd : (embedding m j).hom.hom ≫ snd A₀.X Z.X = j.hom.hom := by
  change lift (kernelι m).hom.hom j.hom.hom ≫ snd A₀.X Z.X = _
  rw [lift_snd]

instance mono_embedding : Mono (embedding m j).hom.hom :=
  mono_of_mono_fac (embedding_hom_fst m j)

theorem isClosedSubgroup_embedding : IsClosedSubgroup (embedding m j) := by
  have : IsSeparated G.X.hom := fieldSeparated k G
  have : IsSeparated Z.X.hom := fieldSeparated k Z.toGrp
  have : IsSeparated (fst A₀.X Z.X).left := by
    change IsSeparated (pullback.fst A₀.X.hom Z.X.hom)
    infer_instance
  have he : (embedding m j).hom.hom.left ≫ (fst A₀.X Z.X).left = (kernelι m).hom.hom.left := by
    rw [← Over.comp_left, embedding_hom_fst]
  have : IsClosedImmersion ((embedding m j).hom.hom.left ≫ (fst A₀.X Z.X).left) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp _ (fst A₀.X Z.X).left

theorem isCentral_embedding (hc : IsCentral (kernelι m)) : IsCentral (embedding m j) := by
  intro T x T' a w
  show _ * _ = _ * _
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc, embedding_hom_fst]
    have h := hc T x T' a (w ≫ fst A₀.X Z.X)
    simpa only [Category.assoc] using h.eq
  · rw [MonObj.mul_comp, MonObj.mul_comp]
    exact mul_comm _ _

end Embedding

section Main

variable {k : Type u} [Field k]

open RelativeRoot in
/-- **Pushout of a central cover along an embedding of its kernel into an induced torus.**

Let `m : A₀ ⟶ G` be a flat surjective homomorphism of connected reductive groups whose kernel
is central, let `c₀ : C ⟶ A₀` be a monic homomorphism from a simply connected group whose
points contain every commutator of `A₀`, and let `j` be a monic homomorphism from the kernel
of `m` into an induced torus `Z`. Then `G` has a z-extension. -/
theorem exists_zExtension_of_centralCover
    {G A₀ C : GroupScheme (Spec (CommRingCat.of k))}
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hA₀ : IsConnectedReductive A₀)
    (m : A₀ ⟶ G) [Flat m.hom.hom.left] [Surjective m.hom.hom.left]
    (hm : IsCentral (kernelι m))
    (c₀ : C ⟶ A₀) [Mono c₀.hom.hom]
    (hc₀ : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ A₀.X),
      ∃ w : T ⟶ C.X, w ≫ c₀.hom.hom = x * y * x⁻¹ * y⁻¹)
    (hC : IsSimplyConnected C)
    (hZ : IsInducedTorus Z) (j : kernel m ⟶ Z.toGrp) [Mono j.hom.hom] :
    Nonempty (ZExtension G) := by
  classical
  -- the induced torus and the product `A₀ × Z`
  have hZt : IsTorus Z.toGrp := by
    obtain ⟨E, _, _, _, _, hs, -⟩ := hZ
    exact ⟨E, _, _, hs⟩
  have hZr : IsConnectedReductive Z.toGrp := hZt.isConnectedReductive_of_fieldSplitting
  have : Smooth Z.toGrp.X.hom := hZr.smooth
  have : IsAffineHom Z.toGrp.X.hom := hZr.isAffineHom
  have : ConnectedSpace Z.toGrp.X.left := hZr.connectedSpace
  have hAr : IsConnectedReductive (A₀ ⊗ Z.toGrp) :=
    (directProductReductive k A₀ Z.toGrp).2.1 hA₀ hZr
  have : Smooth (A₀ ⊗ Z.toGrp).X.hom := hAr.smooth
  have : IsAffineHom (A₀ ⊗ Z.toGrp).X.hom := hAr.isAffineHom
  have hnc : IsCentral (embedding m j) := isCentral_embedding m j hm
  -- the quotient `H = (A₀ × Z) / K`
  obtain ⟨H, q, hHs, hHa, hq⟩ := normalSubgroupQuotient k (A₀ ⊗ Z.toGrp) (kernel m)
    (embedding m j) (isClosedSubgroup_embedding m j) hnc.range_isNormal
  have : Smooth H.X.hom := hHs
  have : IsAffineHom H.X.hom := hHa
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : QuasiCompact q.hom.hom.left := by
    have : IsSeparated H.X.hom := fieldSeparated k H
    have : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp q.hom.hom.left H.X.hom
  have hHr : IsConnectedReductive H :=
    centralQuotientReductive k (A₀ ⊗ Z.toGrp) H q (SubgroupFunctor.range (embedding m j)) hAr
      hHa inferInstance ((isCentral_iff_range_le_center _).mp hnc) hq
  have : ConnectedSpace H.X.left := hHr.connectedSpace
  have hker : ∀ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ (A₀ ⊗ Z.toGrp).X),
      g ≫ q.hom.hom = 1 ↔ ∃ κ : T ⟶ (kernel m).X, κ ≫ (embedding m j).hom.hom = g := by
    intro T g
    rw [← mem_range_kernelι_iff q g, hq.2.2.2]
    exact SubgroupFunctor.mem_range
  have hnq : ∀ {T : Over (Spec (CommRingCat.of k))} (κ : T ⟶ (kernel m).X),
      κ ≫ (embedding m j).hom.hom ≫ q.hom.hom = 1 := fun κ => by
    rw [← Category.assoc]
    exact (hker _).mpr ⟨κ, rfl⟩
  -- the descended homomorphism `p : H ⟶ G`
  let m' : A₀ ⊗ Z.toGrp ⟶ G := fst A₀ Z.toGrp ≫ m
  have hk : kernelι q ≫ m' = 0 := by
    apply Grp.hom_ext
    change (kernelι q).hom.hom ≫ (fst A₀.X Z.X ≫ m.hom.hom) = 1
    obtain ⟨κ, hκ⟩ := (hker _).mp (kernelι_comp_eq_one q)
    rw [← hκ, Category.assoc, embedding_hom_fst_assoc, ← Category.assoc]
    exact (mem_range_kernelι_iff m _).mp (SubgroupFunctor.mem_range.mpr ⟨κ, rfl⟩)
  let p : H ⟶ G := FpqcHomDescent.hom q m' hk
  have hp' : q.hom.hom ≫ p.hom.hom = fst A₀.X Z.X ≫ m.hom.hom := by
    rw [← Grp.comp_hom_hom, FpqcHomDescent.fac]
    rfl
  -- `p` is flat, surjective and locally of finite presentation
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, inc, fac, hinc, hfac, hf, hs, -, hl, -, -, -⟩ := HomImage.exists_image p
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Epi m.hom.hom := by
    have : Epi m.hom.hom.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have : IsSplitEpi (fst A₀.X Z.X) :=
    IsSplitEpi.mk' ⟨(prodInl A₀ Z.toGrp).hom.hom, prodInl_hom_fst A₀ Z.toGrp⟩
  have : Epi inc.hom.hom := by
    have : Epi ((q.hom.hom ≫ fac.hom.hom) ≫ inc.hom.hom) := by
      have e : (q.hom.hom ≫ fac.hom.hom) ≫ inc.hom.hom = fst A₀.X Z.X ≫ m.hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom fac inc, hfac, hp']
      rw [e]
      infer_instance
    exact epi_of_epi (q.hom.hom ≫ fac.hom.hom) inc.hom.hom
  have : IsIso inc.hom.hom := isIso_of_isClosedImmersion_of_epi_over inc.hom.hom
  have : IsIso inc.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map inc.hom.hom))
  have hpl : p.hom.hom.left = fac.hom.hom.left ≫ inc.hom.hom.left := by
    rw [← hfac]
    rfl
  have : Flat fac.hom.hom.left := hf
  have : Surjective fac.hom.hom.left := hs
  have : LocallyOfFinitePresentation fac.hom.hom.left := hl
  have : Flat p.hom.hom.left := by rw [hpl]; infer_instance
  have : Surjective p.hom.hom.left := by rw [hpl]; infer_instance
  have : LocallyOfFinitePresentation p.hom.hom.left := by rw [hpl]; infer_instance
  -- the central torus `Z ⟶ H`
  let iS : Z.toGrp ⟶ H := prodInr A₀ Z.toGrp ≫ q
  have hiS : iS.hom.hom = (prodInr A₀ Z.toGrp).hom.hom ≫ q.hom.hom := rfl
  have hiSc : IsCentral iS := (isCentral_prodInr A₀ Z).comp_flat_surjective q
  have : Mono iS.hom.hom := by
    apply mono_of_comp_eq_one
    intro T s hs
    rw [hiS, ← Category.assoc] at hs
    obtain ⟨κ, hκ⟩ := (hker _).mp hs
    have h1 : κ ≫ (kernelι m).hom.hom = 1 := by
      rw [← embedding_hom_fst m j, ← Category.assoc, hκ, Category.assoc, prodInr_hom_fst,
        MonObj.comp_one]
    have h2 : κ = 1 := by
      apply (cancel_mono (kernelι m).hom.hom).mp
      rw [h1, MonObj.one_comp]
    have h3 : (κ ≫ (embedding m j).hom.hom) ≫ snd A₀.X Z.X =
        (s ≫ (prodInr A₀ Z.toGrp).hom.hom) ≫ snd A₀.X Z.X := by rw [hκ]
    rw [Category.assoc, Category.assoc, embedding_hom_snd, prodInr_hom_snd,
      Category.comp_id, h2, MonObj.one_comp] at h3
    exact h3.symm
  have hiScl : IsClosedSubgroup iS := HomImage.isClosedSubgroup_of_mono iS
  -- exactness: the kernel of `p` is the image of `Z`
  have hpq : IsFppfQuotient (SubgroupFunctor.range iS) p := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [mem_range_kernelι_iff]
    constructor
    · intro hx
      apply SubgroupFunctor.mem_range_of_local_quotient_lift q iS x x
      intro V a g hag
      have hg : (g ≫ fst A₀.X Z.X) ≫ m.hom.hom = 1 := by
        rw [Category.assoc, ← hp', ← Category.assoc, ← hag, Category.assoc, hx,
          MonObj.comp_one]
      obtain ⟨κ, hκ⟩ := Dynamic.exists_kernel_point m _ hg
      obtain ⟨s, hs⟩ : ∃ s : V ⟶ Z.X, s = (κ ≫ j.hom.hom)⁻¹ * (g ≫ snd A₀.X Z.X) :=
        ⟨_, rfl⟩
      have hdec : g = (κ ≫ (embedding m j).hom.hom : V ⟶ (A₀ ⊗ Z.toGrp).X) *
          (s ≫ (prodInr A₀ Z.toGrp).hom.hom : V ⟶ (A₀ ⊗ Z.toGrp).X) := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [MonObj.mul_comp, Category.assoc, Category.assoc, embedding_hom_fst,
            prodInr_hom_fst, MonObj.comp_one, mul_one]
          exact hκ.symm
        · rw [MonObj.mul_comp, Category.assoc, Category.assoc, embedding_hom_snd,
            prodInr_hom_snd, Category.comp_id, hs, mul_inv_cancel_left]
      refine SubgroupFunctor.mem_range.mpr ⟨s, ?_⟩
      rw [hag, hdec, MonObj.mul_comp, Category.assoc, hnq, one_mul, hiS, Category.assoc]
    · intro hx
      obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      rw [Category.assoc, hiS, Category.assoc, hp', prodInr_hom_fst_assoc, MonObj.one_comp,
        MonObj.comp_one]
  -- the simply connected derived group `C ⟶ H`
  have hCr : IsConnectedReductive C := hC.isSemisimple.isConnectedReductive
  have : Smooth C.X.hom := hCr.smooth
  have : IsAffineHom C.X.hom := hCr.isAffineHom
  have : ConnectedSpace C.X.left := hCr.connectedSpace
  let c : C ⟶ H := c₀ ≫ prodInl A₀ Z.toGrp ≫ q
  have hch : c.hom.hom = c₀.hom.hom ≫ (prodInl A₀ Z.toGrp).hom.hom ≫ q.hom.hom := rfl
  have : Mono c.hom.hom := by
    apply mono_of_comp_eq_one
    intro T y hy
    rw [hch, ← Category.assoc, ← Category.assoc] at hy
    obtain ⟨κ, hκ⟩ := (hker _).mp hy
    have h1 : κ ≫ j.hom.hom = 1 := by
      rw [← embedding_hom_snd m j, ← Category.assoc, hκ, Category.assoc, prodInl_hom_snd,
        MonObj.comp_one]
    have h2 : κ = 1 := by
      apply (cancel_mono j.hom.hom).mp
      rw [h1, MonObj.one_comp]
    have h3 : (κ ≫ (embedding m j).hom.hom) ≫ fst A₀.X Z.X =
        ((y ≫ c₀.hom.hom) ≫ (prodInl A₀ Z.toGrp).hom.hom) ≫ fst A₀.X Z.X := by rw [hκ]
    rw [Category.assoc, embedding_hom_fst, h2, MonObj.one_comp, Category.assoc,
      prodInl_hom_fst, Category.comp_id] at h3
    apply (cancel_mono c₀.hom.hom).mp
    rw [← h3, MonObj.one_comp]
  have hccl : IsClosedSubgroup c := HomImage.isClosedSubgroup_of_mono c
  have hcomm : (SubgroupFunctor.range c).ContainsCommutators := by
    intro T x y
    apply SubgroupFunctor.mem_range_of_local_quotient_lift q c x
    intro V a g hag
    apply SubgroupFunctor.mem_range_of_local_quotient_lift q c (a ≫ y)
    intro V' b g' hbg
    obtain ⟨w, hw⟩ := hc₀ V' ((b ≫ g) ≫ fst A₀.X Z.X) (g' ≫ fst A₀.X Z.X)
    refine SubgroupFunctor.mem_range.mpr ⟨w, ?_⟩
    have hx : b ≫ a ≫ x = (b ≫ g) ≫ q.hom.hom := by rw [hag, Category.assoc]
    have hA : (b ≫ g) * g' * (b ≫ g)⁻¹ * g'⁻¹ =
        (w ≫ c₀.hom.hom) ≫ (prodInl A₀ Z.toGrp).hom.hom := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, prodInl_hom_fst, Category.comp_id, hw]
        simp only [MonObj.mul_comp, GrpObj.inv_comp]
      · rw [Category.assoc, prodInl_hom_snd, MonObj.comp_one]
        simp only [MonObj.mul_comp, GrpObj.inv_comp]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
        exact mul_comm _ _
    rw [hch, ← Category.assoc, ← Category.assoc, ← hA]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp]
    rw [hx, hbg]
  have hCperf : derivedSubgroup C = ⊤ := semisimplePerfect k C hC.isSemisimple
  have hder : IsDerivedSubgroup c := by
    refine ⟨hccl, le_antisymm ?_ (derivedSubgroup_le_range c hccl hcomm)⟩
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro H' i' hi' hcomm'
    have hP : (SubgroupFunctor.range (subgroupIntersectionFst c i')).ContainsCommutators := by
      rw [range_subgroupIntersectionFst_eq_comap]
      intro T u v
      rw [SubgroupFunctor.mem_comap]
      simp only [MonObj.mul_comp, GrpObj.inv_comp]
      exact hcomm' T _ _
    have hy : y ∈ (derivedSubgroup C).carrier T := by
      rw [hCperf]
      exact Subgroup.mem_top _
    have h := derivedSubgroup_le_range _ (isClosedSubgroup_subgroupIntersectionFst c hi') hP T hy
    rw [range_subgroupIntersectionFst_eq_comap, SubgroupFunctor.mem_comap] at h
    exact h
  exact ⟨{ Z := Z, H := H, i := iS, p := p, isZExtension :=
    { induced := hZ
      closed := hiScl
      central := hiSc
      quotient := hpq
      source_reductive := hHr
      target_reductive := hG
      derived_simplyConnected := ⟨C, c, hder, hC⟩ } }⟩

end Main

end ZExtensionPushout

end Langlands.GroupScheme
