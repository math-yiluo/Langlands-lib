import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialAdditivity

/-! # Invariance of top coherent Euler coefficients under line-bundle twists -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules QuasicoherentLocal

local instance {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (N : Picard.LineBundle X) :
    (tensorObj M N.obj).IsQuasicoherent :=
  isQuasicoherent_tensor_lineBundle M N.obj N.property

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The coefficient at the common support bound is unchanged by tensoring
the coefficient sheaf with an actual line bundle. -/
def TopEulerCoefficientTwistInvariant
    (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L N : Picard.LineBundle X) (d : ℕ) : Prop :=
  (coherentEulerPolynomial f (tensorObj M N.obj)
    (hM.tensor_lineBundle N.property) L d).coeff d =
      (coherentEulerPolynomial f M hM L d).coeff d

/-- Tensoring an exact coherent sequence by a line bundle gives additivity
of the actual twisted Euler sequences. -/
theorem coherentEulerSequence_add_tensor (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : HasFiniteAffineSections S.X₁) (h₂ : HasFiniteAffineSections S.X₂)
    (h₃ : HasFiniteAffineSections S.X₃) (L N : Picard.LineBundle X) :
    coherentEulerSequence f (tensorObj S.X₂ N.obj) (h₂.tensor_lineBundle N.property) L =
      coherentEulerSequence f (tensorObj S.X₁ N.obj) (h₁.tensor_lineBundle N.property) L +
        coherentEulerSequence f (tensorObj S.X₃ N.obj) (h₃.tensor_lineBundle N.property) L := by
  have := tensorBy_isEquivalence N.obj N.property
  let T := S.map (tensorBy N.obj)
  have : T.X₁.IsQuasicoherent :=
    inferInstanceAs (tensorObj S.X₁ N.obj).IsQuasicoherent
  have : T.X₂.IsQuasicoherent :=
    inferInstanceAs (tensorObj S.X₂ N.obj).IsQuasicoherent
  have : T.X₃.IsQuasicoherent :=
    inferInstanceAs (tensorObj S.X₃ N.obj).IsQuasicoherent
  exact coherentEulerSequence_add f T (shortExact_tensorBy S hS N.obj N.property)
    (h₁.tensor_lineBundle N.property) (h₂.tensor_lineBundle N.property)
    (h₃.tensor_lineBundle N.property) L

/-- A line-bundle twist is invisible to the top Euler difference on a closed
support of the indicated height bound. -/
theorem iterate_fwdDiff_tensor_sub_eq_zero_of_height [IsNoetherian X] [X.IsSeparated]
    (d : ℕ) :
    ∀ (Z : Closeds X) (M : X.Modules) [M.IsQuasicoherent]
      (hM : HasFiniteAffineSections M) (L N : Picard.LineBundle X),
      VanishesOn M Z.compl →
      (∀ T : IrreducibleCloseds X, (T : Set X) ⊆ Z → height T ≤ d) →
      (fwdDiff 1)^[d]
        (coherentEulerSequence f (tensorObj M N.obj) (hM.tensor_lineBundle N.property) L -
          coherentEulerSequence f M hM L) = 0 := by
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z IH =>
    intro M _ hM L N hMZ hZ
    by_cases hZe : (Z : Set X) = ∅
    · have hz : IsZero M := NoetherianVanishing.isZero_of_vanishesOn_top
        (hMZ.mono (fun x _ hx => by
          simp only [hZe, Set.mem_empty_iff_false] at hx))
      have htz := ((HasSupportDimensionLT.of_isZero hz 0).tensor_lineBundle N.property).isZero
      rw [coherentEulerSequence_zero f M hM L hz,
        coherentEulerSequence_zero f _ _ L htz, sub_self, iterate_fwdDiff_zero]
    obtain ⟨T, O, hTZ, ⟨η, hηO, hηZ⟩, hOT⟩ :=
      NoetherianVanishing.exists_irreducibleCloseds_inter_subset Z
        (Set.nonempty_iff_ne_empty.2 hZe)
    obtain ⟨W, hηW, ⟨t⟩⟩ := N.property η
    obtain ⟨V, hV, hηV, hVOW⟩ :=
      (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show η ∈ O ⊓ W from ⟨hηO, hηW⟩)
    change X.Opens at V
    have hVO : V ≤ O := hVOW.trans inf_le_left
    let tV : N.obj.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app N.obj ≪≫
        Picard.pullbackTrivializationOfLE (hVOW.trans inf_le_right) N.obj t
    have := isAffineHom_affineOpen_ι hV
    let J := (Scheme.Modules.pushforward V.ι).obj (M.restrict V.ι)
    have : J.IsQuasicoherent := isQuasicoherent_pushforward V.ι (M.restrict V.ι)
    let φ : M ⟶ J := unitMap V.ι M
    let p := factorThruImage φ
    let i := image.ι φ
    have := isQuasicoherent_image φ
    have := isQuasicoherent_kernel p
    have hI : HasFiniteAffineSections (image φ) := hM.of_epi p
    have hK : HasFiniteAffineSections (kernel p) := hM.kernel p
    let Z' : Closeds X :=
      ⟨(Z : Set X) ∩ (V : Set X)ᶜ, Z.isClosed.inter V.isOpen.isClosed_compl⟩
    have hZ'Z : Z' < Z := by
      refine lt_of_le_of_ne (fun x hx => hx.1) (fun h => ?_)
      have : η ∈ (Z' : Set X) := by rw [h]; exact hηZ
      exact this.2 hηV
    have eK : kernel φ ≅ kernel p :=
      (kernelIsoOfEq (image.fac φ)).symm ≪≫ kernelCompMono p i
    have hKsupp : VanishesOn (kernel p) Z'.compl := by
      have h1 : VanishesOn (kernel φ) (Z.compl ⊔ V) :=
        (hMZ.kernel φ).sup
          ((Scheme.Opens.opensRange_ι V) ▸ vanishesOn_kernel_unitMap V.ι M)
      refine (h1.mono ?_).of_iso eK
      intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inr hxV
      · exact Or.inl (fun hxZ => hx ⟨hxZ, hxV⟩)
    have hKzero := IH Z' hZ'Z (kernel p) hK L N hKsupp
      (fun S hS => hZ S (hS.trans (fun x hx => hx.1)))
    let Tc : X.Opens := ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩
    have hJT : VanishesOn J Tc := by
      refine vanishesOn_pushforward_restrict V.ι M hMZ (fun A hA => ?_)
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      rintro x ⟨hxV, hxA⟩ hxZ
      exact hA hxA (hOT ⟨hVO hxV, hxZ⟩)
    have hIT : VanishesOn (image φ) Tc := hJT.of_mono i
    have hNT : VanishesOn (tensorObj (image φ) N.obj) Tc := by
      apply VanishesOn.of_stalkSupport_subset_compl
      rw [stalkSupport_tensor_lineBundle (image φ) N.obj N.property]
      exact hIT.stalkSupport_subset_compl
    have hIzero := iterate_fwdDiff_sub_of_irreducible f d
      (image φ) (tensorObj (image φ) N.obj) hI (hI.tensor_lineBundle N.property)
      L T (hZ T hTZ) V hV ⟨η, hOT ⟨hηO, hηZ⟩, hηV⟩ hIT hNT
      (tensorRestrictionTrivialization (image φ) N.obj V tV)
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    have hadd := coherentEulerSequence_add f S hS hK hM hI L
    have htadd := coherentEulerSequence_add_tensor f S hS hK hM hI L N
    change coherentEulerSequence f M hM L = _ at hadd
    change coherentEulerSequence f (tensorObj M N.obj) _ L = _ at htadd
    have heq :
        coherentEulerSequence f (tensorObj M N.obj) (hM.tensor_lineBundle N.property) L -
          coherentEulerSequence f M hM L =
        (coherentEulerSequence f (tensorObj (kernel p) N.obj)
            (hK.tensor_lineBundle N.property) L - coherentEulerSequence f (kernel p) hK L) +
          (coherentEulerSequence f (tensorObj (image φ) N.obj)
            (hI.tensor_lineBundle N.property) L - coherentEulerSequence f (image φ) hI L) := by
      rw [hadd, htadd]
      abel
    rw [heq, fwdDiff_iter_add, hKzero, hIzero, add_zero]

/-- The support bound makes a line-bundle twist invisible to the top difference. -/
theorem iterate_fwdDiff_tensor_sub_eq_zero [IsNoetherian X] [X.IsSeparated]
    (d : ℕ) (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L N : Picard.LineBundle X) (h : HasSupportDimensionLT M (d + 1)) :
    (fwdDiff 1)^[d]
      (coherentEulerSequence f (tensorObj M N.obj) (hM.tensor_lineBundle N.property) L -
        coherentEulerSequence f M hM L) = 0 := by
  obtain ⟨Z, hMZ, hZ⟩ := h
  apply iterate_fwdDiff_tensor_sub_eq_zero_of_height f d Z M hM L N hMZ
  intro T hT
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mp (hZ T hT)

/-- The top coherent Euler coefficient is unchanged by arbitrary line-bundle
twists, including at support dimension zero. -/
theorem topEulerCoefficientTwistInvariant [IsNoetherian X] [X.IsSeparated]
    (d : ℕ) (M : X.Modules) [M.IsQuasicoherent] (hM : HasFiniteAffineSections M)
    (L N : Picard.LineBundle X) (h : HasSupportDimensionLT M (d + 1)) :
    TopEulerCoefficientTwistInvariant f M hM L N d := by
  have he := iterate_fwdDiff_tensor_sub_eq_zero f d M hM L N h
  rw [iterate_fwdDiff_sub, sub_eq_zero] at he
  unfold TopEulerCoefficientTwistInvariant coherentEulerPolynomial
  rw [Langlands.Algebra.RationalPolynomial.newtonPolynomial_coeff,
    Langlands.Algebra.RationalPolynomial.newtonPolynomial_coeff, he]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
