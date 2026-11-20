import Langlands.GroupScheme.MatrixRepresentation.LocalCentralKernelStatement
import Langlands.GroupScheme.IdentityJetCentralizerStabilizationStatement
import Langlands.GroupScheme.MatrixRepresentation.JetConjugationRepresentationStatement
import Langlands.GroupScheme.IdentityJetBaseChange
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.AbelianScheme.KernelBaseChange

/-! # Local central-kernel representations from jet representations and stabilisation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

variable {S T : Scheme.{u}} (G : GroupScheme S) (b : T ⟶ S)

/-- The unit section of a separated group scheme is a closed immersion. -/
theorem isClosedImmersion_identitySection [IsSeparated G.X.hom] :
    IsClosedImmersion G.identitySection := by
  let : IsClosedImmersion (G.identitySection ≫ G.X.hom) := by
    rw [G.identitySection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp G.identitySection G.X.hom

/-- For a separated group, jet ideals commute with every base change. -/
theorem ideal_baseChange_of_isSeparated [IsSeparated G.X.hom] (n : ℕ) :
    (ideal G n).comap (pullback.fst G.X.hom b) =
      ideal ((GroupScheme.baseChange b).obj G) n := by
  have : IsClosedImmersion G.identitySection := isClosedImmersion_identitySection G
  have hker : G.identitySection.ker.comap (pullback.fst G.X.hom b) =
      ((GroupScheme.baseChange b).obj G).identitySection.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h := identitySection_isPullback G b
    rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  change (G.identitySection.ker ^ (n + 1)).comap (pullback.fst G.X.hom b) = _
  rw [idealSheaf_comap_pow, hker]
  rfl

/-- The map from the base-changed identity jet to the original one. -/
def jetBaseChangeMap [IsSeparated G.X.hom] (n : ℕ) :
    scheme ((GroupScheme.baseChange b).obj G) n ⟶ scheme G n :=
  Scheme.IdealSheafData.subschemeMap
    (ideal ((GroupScheme.baseChange b).obj G) n) (ideal G n)
    (pullback.fst G.X.hom b)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (ideal_baseChange_of_isSeparated G b n)))

@[reassoc (attr := simp)]
theorem jetBaseChangeMap_inclusion [IsSeparated G.X.hom] (n : ℕ) :
    jetBaseChangeMap G b n ≫ inclusion G n =
      inclusion ((GroupScheme.baseChange b).obj G) n ≫ pullback.fst G.X.hom b :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The base-changed jet is the pullback of the jet along the group projection. -/
theorem jetBaseChange_isPullback [IsSeparated G.X.hom] (n : ℕ) :
    IsPullback (inclusion ((GroupScheme.baseChange b).obj G) n)
      (jetBaseChangeMap G b n) (pullback.fst G.X.hom b) (inclusion G n) := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsClosedImmersion (inclusion ((GroupScheme.baseChange b).obj G) n) :=
    inferInstanceAs (IsClosedImmersion (ideal ((GroupScheme.baseChange b).obj G) n).subschemeι)
  exact isPullback_of_isClosedImmersion _ _ _ _
    (jetBaseChangeMap_inclusion G b n).symm
    (by simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
      ideal_baseChange_of_isSeparated G b n)

/-- Jet points are preserved and reflected by the base-change point equivalence. -/
theorem isJetPoint_baseChange_iff [IsSeparated G.X.hom] (n : ℕ) {V : Over T}
    (x : V ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsJetPoint ((GroupScheme.baseChange b).obj G) n x ↔
      IsJetPoint G n (baseChangePointsEquiv b G V x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ jetBaseChangeMap G b n, ?_⟩
    rw [Category.assoc, jetBaseChangeMap_inclusion, ← Category.assoc, hy]
    rfl
  · rintro ⟨y, hy⟩
    exact ⟨(jetBaseChange_isPullback G b n).lift x.left y hy.symm,
      (jetBaseChange_isPullback G b n).lift_fst _ _ _⟩

variable {G}

/-- Centralizing a jet is preserved by restriction along a morphism of tests. -/
theorem CentralizesJet.comp {n : ℕ} {U U' : Over S} (a : U' ⟶ U) {g : U ⟶ G.X}
    (hg : CentralizesJet G n g) : CentralizesJet G n (a ≫ g) := by
  intro V c x hx
  simpa only [Category.assoc] using hg V (c ≫ a) x hx

/-- A point of the base-changed group centralizing its jet gives a point of the
original group centralizing the original jet. -/
theorem CentralizesJet.of_baseChange [IsSeparated G.X.hom] {n : ℕ} {U : Over T}
    {g : U ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hg : CentralizesJet ((GroupScheme.baseChange b).obj G) n g) :
    CentralizesJet G n (baseChangePointsEquiv b G U g) := by
  intro V' a' x' hx'
  let V : Over T := Over.mk (a'.left ≫ U.hom)
  let a : V ⟶ U := Over.homMk a'.left rfl
  have hV : V'.hom = ((Over.map b).obj V).hom := by
    change V'.hom = (a'.left ≫ U.hom) ≫ b
    rw [Category.assoc]
    exact (Over.w a').symm
  let φ : V' ≅ (Over.map b).obj V := Over.isoMk (Iso.refl _) (by simp [hV])
  let x : V ⟶ ((GroupScheme.baseChange b).obj G).X :=
    (baseChangePointsEquiv b G V).symm (φ.inv ≫ x')
  have hx : IsJetPoint ((GroupScheme.baseChange b).obj G) n x := by
    rw [isJetPoint_baseChange_iff, MulEquiv.apply_symm_apply]
    obtain ⟨y, hy⟩ := hx'
    exact ⟨φ.inv.left ≫ y, by rw [Category.assoc, hy]; rfl⟩
  have h := congrArg (baseChangePointsEquiv b G V) (hg V a x hx)
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality] at h
  have h' := congrArg (φ.hom ≫ ·) h
  simp only [MonObj.comp_mul] at h'
  have ha : φ.hom ≫ (Over.map b).map a = a' := by
    apply Over.OverMorphism.ext
    simp [φ, a]
  have hx'' : φ.hom ≫ φ.inv ≫ x' = x' := by simp
  rw [← Category.assoc, ha, hx''] at h'
  exact h'

/-- A point whose image centralizes the original jet centralizes the base-changed jet. -/
theorem CentralizesJet.baseChange [IsSeparated G.X.hom] {n : ℕ} {U : Over T}
    {g : U ⟶ ((GroupScheme.baseChange b).obj G).X}
    (hg : CentralizesJet G n (baseChangePointsEquiv b G U g)) :
    CentralizesJet ((GroupScheme.baseChange b).obj G) n g := by
  intro V a x hx
  rw [isJetPoint_baseChange_iff] at hx
  have h := hg ((Over.map b).obj V) ((Over.map b).map a) (baseChangePointsEquiv b G V x) hx
  rw [← baseChangePointsEquiv_naturality, ← map_mul, ← map_mul] at h
  exact (baseChangePointsEquiv b G V).injective h

end Langlands.GroupScheme.IdentityJet

namespace Langlands.GroupScheme

open IdentityJet

/-- Local central-kernel representations follow from the conjugation
representations on identity jets and the stabilisation of jet centralizers. -/
theorem localCentralKernelRepresentation_of
    (hstab : JetCentralizerStabilizationStatement.{u})
    (hrep : JetConjugationRepresentationStatement.{u}) :
    LocalCentralKernelRepresentationStatement.{u} := by
  intro S G hsm hsep hqc hconn s
  have : Smooth G.X.hom := hsm
  have : IsSeparated G.X.hom := hsep
  have : QuasiCompact G.X.hom := hqc
  obtain ⟨W, hW, hsW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  let i₁ : Spec Γ(S, W) ⟶ S := hW.fromSpec
  let G₁ := (GroupScheme.baseChange i₁).obj G
  have : Smooth G₁.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom i₁))
  have : IsSeparated G₁.X.hom := inferInstanceAs (IsSeparated (pullback.snd G.X.hom i₁))
  have : QuasiCompact G₁.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom i₁))
  have hconn₁ : ∀ t : Spec Γ(S, W),
      ConnectedSpace (RelativeIdentityComponent.residueFiber G₁ t).X.left := fun t =>
    (ExtensionReduction.connectedSpace_residueFiber_baseChange_iff i₁ G t).mpr (hconn (i₁ t))
  obtain ⟨n, hn⟩ := hstab Γ(S, W) G₁ inferInstance inferInstance inferInstance hconn₁
  obtain ⟨R, i, hi, hsi, hiW, m, ρ, hρ⟩ := hrep S G hsm hsep n s W hsW
  refine ⟨R, i, hi, hsi, m, ρ, fun U g k hg => ?_⟩
  have hcj : CentralizesJet G n (baseChangePointsEquiv i G U g) :=
    CentralizesJet.of_baseChange i ((hρ U g).mp hg)
  have hrange : Set.range (U.hom ≫ i).base ⊆ Set.range i₁.base := by
    rw [hW.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact hiW ⟨U.hom x, rfl⟩
  let c : U.left ⟶ Spec Γ(S, W) := IsOpenImmersion.lift i₁ (U.hom ≫ i) hrange
  have hc : c ≫ i₁ = U.hom ≫ i := IsOpenImmersion.lift_fac _ _ _
  let U₁ : Over (Spec Γ(S, W)) := Over.mk c
  let ψ : (Over.map i₁).obj U₁ ≅ (Over.map i).obj U :=
    Over.isoMk (Iso.refl _) (by simp [U₁, hc])
  let g₁ : U₁ ⟶ G₁.X := (baseChangePointsEquiv i₁ G U₁).symm (ψ.hom ≫ baseChangePointsEquiv i G U g)
  have hcj₁ : CentralizesJet G₁ n g₁ := by
    apply CentralizesJet.baseChange i₁
    rw [MulEquiv.apply_symm_apply]
    exact hcj.comp ψ.hom
  have hcen₁ := hn U₁ g₁ hcj₁
  -- transport centrality to the original group over `(Over.map i).obj U`
  have hcen : ∀ k' : (Over.map i).obj U ⟶ G.X,
      baseChangePointsEquiv i G U g * k' = k' * baseChangePointsEquiv i G U g := by
    intro k'
    have h := congrArg (baseChangePointsEquiv i₁ G U₁)
      (hcen₁ ((baseChangePointsEquiv i₁ G U₁).symm (ψ.hom ≫ k')))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      ← MonObj.comp_mul, ← MonObj.comp_mul] at h
    exact (cancel_epi ψ.hom).mp h
  apply (baseChangePointsEquiv i G U).injective
  rw [map_mul, map_mul]
  exact hcen _

end Langlands.GroupScheme
