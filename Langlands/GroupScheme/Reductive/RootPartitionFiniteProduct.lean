import Langlands.GroupScheme.Reductive.RootPartitionNormalSubgroup
import Langlands.GroupScheme.Reductive.FiniteProductHomKernel
import Langlands.GroupScheme.HomImage

/-! # Actual finite products of commuting root-partition models -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootPartitionFamily

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    {C : Type u} [Finite C] (s : C → Set (characterLattice T))
    (N : ∀ c, RootPartitionNormalModel i (s c))
    (hdisj : Pairwise fun c d => Disjoint (s c) (s d))

include hdisj in
omit [Finite C] in
/-- Distinct root-partition factors commute on every relative test scheme. -/
theorem commutation (Z : Over (Spec (CommRingCat.of k))) :
    Pairwise fun c d => ∀ (x : Z ⟶ (N c).group.X) (y : Z ⟶ (N d).group.X),
      Commute (x ≫ (N c).inclusion.hom.hom) (y ≫ (N d).inclusion.hom.hom) := by
  intro c d hcd x y
  have hx := (N c).range_le_centralizer i (N d) (hdisj hcd) Z
    (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  simpa only [Category.id_comp] using
    hx Z (𝟙 Z) (y ≫ (N d).inclusion.hom.hom)
      (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)

/-- The actual multiplication map of all the supplied root-partition models. -/
def multiplication : pi (fun c => (N c).group) ⟶ G :=
  CommutingFamily.multiplication (fun c => (N c).group) (fun c => (N c).inclusion)
    (commutation i s N hdisj)

/-- Each original inclusion is the exact restriction of finite multiplication. -/
@[reassoc (attr := simp)] theorem inclusion_multiplication (c : C) :
    piFactorInclusionHom (fun c => (N c).group) c ≫ multiplication i s N hdisj =
      (N c).inclusion :=
  CommutingFamily.inclusion_multiplication _ _ _ c

/-- All factor restrictions of actual multiplication are monic. -/
theorem mono_factors : ∀ c, Mono
    (piFactorInclusionHom (fun c => (N c).group) c ≫ multiplication i s N hdisj).hom.hom := by
  intro c
  rw [inclusion_multiplication]
  let : IsClosedImmersion (N c).inclusion.hom.hom.left := (N c).closed
  exact Over.mono_of_mono_left _

variable [IsAlgClosed k]

/-- Covering all roots makes actual finite multiplication surjective. -/
theorem multiplication_surjective (hG : IsSemisimple G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) :
    Surjective (multiplication i s N hdisj).hom.hom.left := by
  have hP := IsSemisimple.pi (fun c => (N c).group) (fun c => (N c).semisimple)
  let : Smooth (pi (fun c => (N c).group)).X.hom := hP.isConnectedReductive.smooth
  let : ConnectedSpace (pi (fun c => (N c).group)).X.left := hP.isConnectedReductive.connectedSpace
  let : IsAffineHom (pi (fun c => (N c).group)).X.hom := hP.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  obtain ⟨Q, q, p, hq, hpq, _, hps, _⟩ := HomImage.exists_image (multiplication i s N hdisj)
  have hfactor : ∀ c, SubgroupFunctor.range (N c).inclusion ≤ SubgroupFunctor.range q := by
    intro c
    apply (CommutingFamily.range_le_multiplication (fun c => (N c).group)
      (fun c => (N c).inclusion) (commutation i s N hdisj) c).trans
    intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hpq]
    rfl
  have htop : SubgroupFunctor.range q = ⊤ := by
    apply semisimpleRootGeneration k G hG T i hsplit hmax Q q hq
    intro α hα
    obtain ⟨c, hc⟩ := hcover α hα
    exact ((N c).contains α hc).trans (hfactor c)
  let : IsClosedImmersion q.hom.hom.left := hq
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy q :=
    ⟨Over.mono_of_mono_left _, htop⟩
  let : IsIso q := by
    rw [← hrep.topIso_hom]
    infer_instance
  let : IsIso q.hom.hom.left :=
    (Over.forget _).map_isIso ((Grp.forget _).map q)
  let : Surjective q.hom.hom.left := inferInstance
  let : Surjective p.hom.hom.left := hps
  have hs : Surjective (p.hom.hom.left ≫ q.hom.hom.left) := inferInstance
  rwa [← Over.comp_left, ← Grp.comp_hom_hom, hpq] at hs

/-- The actual finite multiplication is a central isogeny when the parts cover all roots. -/
theorem multiplication_isCentralIsogeny (hG : IsSemisimple G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) :
    IsCentralIsogeny (multiplication i s N hdisj) :=
  isCentralIsogeny_piHom_of_surjective (fun c => (N c).group)
    (multiplication i s N hdisj) (fun c => (N c).semisimple)
    hG.isConnectedReductive (mono_factors i s N hdisj)
    (multiplication_surjective i s N hdisj hG hsplit hmax hcover)

/-- A simply connected ambient group is the actual product of its supplied
pairwise disjoint root-generated factors covering all roots. -/
def simplyConnectedIso (hG : IsSimplyConnected G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) :
    pi (fun c => (N c).group) ≅ G := by
  let : IsIso (multiplication i s N hdisj) :=
    isIso_piHom_of_isSimplyConnected (fun c => (N c).group) (multiplication i s N hdisj)
      (fun c => (N c).semisimple) hG (mono_factors i s N hdisj)
      (multiplication_surjective i s N hdisj hG.isSemisimple hsplit hmax hcover)
  exact asIso (multiplication i s N hdisj)

/-- An adjoint ambient group is the actual product of the same supplied factors. -/
def adjointIso (hG : IsSemisimple G) (hc : center G = ⊥)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) :
    pi (fun c => (N c).group) ≅ G := by
  let : IsIso (multiplication i s N hdisj) :=
    isIso_piHom_of_isAdjoint (fun c => (N c).group) (multiplication i s N hdisj)
      (fun c => (N c).semisimple) ⟨hG, hc⟩ (mono_factors i s N hdisj)
      (multiplication_surjective i s N hdisj hG hsplit hmax hcover)
  exact asIso (multiplication i s N hdisj)

/-- The simply connected product isomorphism retains every original inclusion. -/
@[reassoc (attr := simp)] theorem inclusion_simplyConnectedIso_hom (hG : IsSimplyConnected G)
    (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) (c : C) :
    piFactorInclusionHom (fun c => (N c).group) c ≫
      (simplyConnectedIso i s N hdisj hG hsplit hmax hcover).hom = (N c).inclusion :=
  inclusion_multiplication i s N hdisj c

/-- The adjoint product isomorphism retains every original inclusion. -/
@[reassoc (attr := simp)] theorem inclusion_adjointIso_hom (hG : IsSemisimple G)
    (hc : center G = ⊥) (hsplit : IsSplitSubtorus i) (hmax : IsMaximalTorus i)
    (hcover : ∀ α ∈ relativeRoots i, ∃ c, α ∈ s c) (c : C) :
    piFactorInclusionHom (fun c => (N c).group) c ≫
      (adjointIso i s N hdisj hG hc hsplit hmax hcover).hom = (N c).inclusion :=
  inclusion_multiplication i s N hdisj c

end Langlands.GroupScheme.RootPartitionFamily
