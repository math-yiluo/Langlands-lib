import Langlands.AlgebraicGeometry.Modules.CoherentGraph

/-! # Coherent graphs and smaller support errors -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules

open QuasicoherentLocal

variable {X : Scheme.{u}}

/-- Removing an open meeting an irreducible closed set lowers its support-height bound. -/
lemma HasSupportDimensionLT.of_irreducible_vanishesOn {M : X.Modules}
    (T : IrreducibleCloseds X) {e : ℕ} (hT : height T ≤ e) (U : X.Opens)
    (hTU : ((T : Set X) ∩ U).Nonempty)
    (hM : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hMU : VanishesOn M U) : HasSupportDimensionLT M e := by
  let Z : Closeds X :=
    ⟨(T : Set X) ∩ (U : Set X)ᶜ, T.isClosed.inter U.isOpen.isClosed_compl⟩
  refine ⟨Z, (hM.sup hMU).mono ?_, ?_⟩
  · intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inr hxU
    · exact Or.inl (fun hxT => hx ⟨hxT, hxU⟩)
  · intro S hS
    obtain ⟨x, hxT, hxU⟩ := hTU
    have hST : height S + 1 ≤ height T :=
      NoetherianVanishing.height_add_one_le_of_subset
        (fun y hy => (hS hy).1) hxT (fun hx => (hS hx).2 hxU)
    exact (ENat.add_one_le_iff' (ENat.natCast_ne_top e)).1 (hST.trans hT)

/-- A map invertible on an open meeting its irreducible source support has smaller kernel. -/
lemma HasSupportDimensionLT.kernel_of_irreducible_isIso {M N : X.Modules}
    (φ : M ⟶ N) (T : IrreducibleCloseds X) {e : ℕ} (hT : height T ≤ e)
    (U : X.Opens) (hTU : ((T : Set X) ∩ U).Nonempty)
    (hM : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    HasSupportDimensionLT (Limits.kernel φ) e :=
  .of_irreducible_vanishesOn T hT U hTU (hM.kernel φ) (.kernel_of_isIso φ hφ)

/-- A map invertible on an open meeting its irreducible target support has smaller cokernel. -/
lemma HasSupportDimensionLT.cokernel_of_irreducible_isIso {M N : X.Modules}
    (φ : M ⟶ N) (T : IrreducibleCloseds X) {e : ℕ} (hT : height T ≤ e)
    (U : X.Opens) (hTU : ((T : Set X) ∩ U).Nonempty)
    (hN : VanishesOn N ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    HasSupportDimensionLT (Limits.cokernel φ) e :=
  .of_irreducible_vanishesOn T hT U hTU
    (.cokernel_of_right φ hN) (.cokernel_of_isIso φ hφ)

/-- On a separated scheme, the inclusion of an affine open is an affine morphism. -/
lemma isAffineHom_affineOpen_ι [X.IsSeparated] {U : X.Opens} (hU : IsAffineOpen U) :
    IsAffineHom U.ι := by
  have := NoetherianVanishing.isAffineHom_fromSpec hU
  rw [← hU.isoSpec_hom_fromSpec]
  infer_instance

namespace CoherentGraph

variable (M N : X.Modules) (U : X.Opens) (e : N.restrict U.ι ≅ M.restrict U.ι)

/-- The graph over an affine open of a separated scheme is quasi-coherent. -/
lemma isQuasicoherent [X.IsSeparated] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) : (graph M N U e).IsQuasicoherent := by
  have := isAffineHom_affineOpen_ι hU
  have := QuasicoherentLocal.isQuasicoherent_pushforward U.ι (M.restrict U.ι)
  exact QuasicoherentLocal.isQuasicoherent_pullback _ _

/-- The graph of two modules finite on affine opens is finite on affine opens. -/
lemma hasFiniteAffineSections [IsLocallyNoetherian X]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N) :
    HasFiniteAffineSections (graph M N U e) :=
  hM.pullback _ _ hN

/-- The four graph errors are quasi-coherent over an affine open of a separated scheme. -/
lemma isQuasicoherent_errors [X.IsSeparated] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    (kernel (fst M N U e)).IsQuasicoherent ∧
      (cokernel (fst M N U e)).IsQuasicoherent ∧
      (kernel (snd M N U e)).IsQuasicoherent ∧
      (cokernel (snd M N U e)).IsQuasicoherent := by
  have := isQuasicoherent M N U e hU
  exact ⟨QuasicoherentLocal.isQuasicoherent_kernel _,
    QuasicoherentLocal.isQuasicoherent_cokernel _,
    QuasicoherentLocal.isQuasicoherent_kernel _,
    QuasicoherentLocal.isQuasicoherent_cokernel _⟩

/-- The four graph errors have finite affine sections under coherent noetherian hypotheses. -/
lemma hasFiniteAffineSections_errors [X.IsSeparated] [IsLocallyNoetherian X]
    [M.IsQuasicoherent] [N.IsQuasicoherent] (hU : IsAffineOpen U)
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N) :
    HasFiniteAffineSections (kernel (fst M N U e)) ∧
      HasFiniteAffineSections (cokernel (fst M N U e)) ∧
      HasFiniteAffineSections (kernel (snd M N U e)) ∧
      HasFiniteAffineSections (cokernel (snd M N U e)) := by
  have := isQuasicoherent M N U e hU
  have hG := hasFiniteAffineSections M N U e hM hN
  exact ⟨hG.kernel _, hM.cokernel _, hG.kernel _, hN.cokernel _⟩

/-- The graph vanishes wherever both modules vanish. -/
lemma vanishesOn {O : X.Opens} (hM : VanishesOn M O) (hN : VanishesOn N O) :
    VanishesOn (graph M N U e) O := by
  have : Mono (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct
      (unitMap U.ι M) (comparisonMap M N U e)) :=
    Fork.IsLimit.mono (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _)
  exact (hM.biprod hN).of_mono
    (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct _ _)

/-- Each kernel and cokernel of the two graph projections has support-height bound `d`. -/
def HasSupportErrorsLT (d : ℕ) : Prop :=
    HasSupportDimensionLT (kernel (fst M N U e)) d ∧
      HasSupportDimensionLT (cokernel (fst M N U e)) d ∧
      HasSupportDimensionLT (kernel (snd M N U e)) d ∧
      HasSupportDimensionLT (cokernel (snd M N U e)) d

/-- All four errors of the graph projections have strictly smaller support height. -/
lemma lowerSupportErrors (T : IrreducibleCloseds X) {d : ℕ} (hT : height T ≤ d)
    (hTU : ((T : Set X) ∩ U).Nonempty)
    (hM : VanishesOn M ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hN : VanishesOn N ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩) :
    HasSupportErrorsLT M N U e d := by
  have hG := vanishesOn M N U e hM hN
  exact ⟨.kernel_of_irreducible_isIso _ T hT U hTU hG (isIso_restrict_fst M N U e),
    .cokernel_of_irreducible_isIso _ T hT U hTU hM (isIso_restrict_fst M N U e),
    .kernel_of_irreducible_isIso _ T hT U hTU hG (isIso_restrict_snd M N U e),
    .cokernel_of_irreducible_isIso _ T hT U hTU hN (isIso_restrict_snd M N U e)⟩

end CoherentGraph

end Langlands.AlgebraicGeometry.Modules
