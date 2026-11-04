import Langlands.GroupScheme.FlagCoreTorus
import Langlands.GroupScheme.FlagCoreFixedLine
import Langlands.GroupScheme.FlagCoreDualLine
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Assembly of the covering core of the flag step -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FlagCore

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational points of `G` that come from rational points of `U` through `i : U ⟶ G`. -/
def rationalImage {U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ G) :
    Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  Set.range fun x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X => x ≫ i.hom.hom

variable {m : Type} [Fintype m] [DecidableEq m]

/-- A line stabilized by `b` on all tests is stabilized by the rational points of `b`. -/
theorem StabilizesLine.rational {σ : MatrixRepresentation G m} {v : m → k}
    {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G} (hs : StabilizesLine σ v b)
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    (hx : x ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ∃ c : k, (σ.rationalMatrix x : Matrix m m k) *ᵥ v = c • v := by
  obtain ⟨a, ha⟩ := hs _ x hx
  have hv : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ∘
      (fun i => scalarMap (Over.mk (𝟙 (Spec (CommRingCat.of k)))) (v i)) = v :=
    funext fun i => ΓSpecIso_hom_scalarMap (v i)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    (a : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)), funext fun i => ?_⟩
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (congrFun ha i)
  rw [RingHom.map_mulVec, hv, Pi.smul_apply, smul_eq_mul, map_mul] at h
  rw [rationalMatrix_coe, h, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact ΓSpecIso_hom_scalarMap (v i)

/-- If the Borel subgroup `b` is the stabilizer of the coordinate line `j` on all tests, it
stabilizes that line in the sense of `StabilizesLine`. -/
theorem stabilizesLine_single {B : GroupScheme (Spec (CommRingCat.of k))} {b : B ⟶ G}
    (ρ : MatrixRepresentation G m) (j : m)
    (hstab : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) : m → Γ(Z.left, ⊤))) :
    StabilizesLine ρ (Pi.single j 1) b := by
  intro Z x hx
  obtain ⟨a, ha⟩ := (hstab Z x).mp hx
  have hsc : (fun l => scalarMap Z ((Pi.single j (1 : k) : m → k) l)) =
      (Pi.single j (1 : Γ(Z.left, ⊤)) : m → Γ(Z.left, ⊤)) := by
    funext l
    by_cases hl : l = j
    · subst hl
      rw [Pi.single_eq_same, Pi.single_eq_same, map_one]
    · rw [Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl, map_zero]
  exact ⟨a, by rw [hsc]; exact ha⟩

variable [IsAlgClosed k]

/-- **The torus moved into `B`.** If `B` is the stabilizer of the coordinate line `j` and the
line of `ρ(g) e_j` is fixed by the rational points `τ s` of the maximal torus `t`, then the
conjugate `g⁻¹ t g` lies in `B` on all tests. -/
theorem range_conj_le_of_isTorusFixed {B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} (ht : IsMaximalTorus t)
    {b : B ⟶ G} (hb : IsBorelSubgroup b) (ρ : MatrixRepresentation G m) (j : m)
    (hstab : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) : m → Γ(Z.left, ⊤)))
    {I : Type*} [Fintype I] (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hτ : Set.range τ =
      Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X => z ≫ t.hom.hom)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix (Pi.single j 1) g)) :
    SubgroupFunctor.range (t ≫ (G.innerIso g⁻¹).hom) ≤ SubgroupFunctor.range b := by
  have hrat : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      y ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ↔
        ∃ c : k, (ρ.rationalMatrix y : Matrix m m k) *ᵥ Pi.single j 1 = c • Pi.single j 1 :=
    fun y => (hstab _ y).trans (exists_unit_pointMatrix_iff ρ j y)
  have hto : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (∃ c : k, (ρ.rationalMatrix y : Matrix m m k) *ᵥ
          orbitVec ρ.rationalMatrix (Pi.single j 1) g =
        c • orbitVec ρ.rationalMatrix (Pi.single j 1) g) →
      g⁻¹ * y * g ∈ (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rintro y ⟨c, hc⟩
    refine (hrat _).mpr ⟨c, ?_⟩
    unfold orbitVec at hc
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc,
      mulVec_smul, mulVec_mulVec, map_inv, Units.inv_mul, one_mulVec]
  have hTs : Smooth T.toGrp.X.hom := IsTorus.smooth ht.1
  have : IsReduced T.toGrp.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k T.toGrp.X.left T.toGrp.X.hom
  apply SubgroupFunctor.range_le_of_algClosed_points hb.isClosedSubgroup
  intro y hy
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  obtain ⟨s, hs⟩ : z ≫ t.hom.hom ∈ Set.range τ := by
    rw [hτ]
    exact ⟨z, rfl⟩
  have h := hto (τ s) (hg s)
  rw [hs] at h
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, constantPoint_inv,
    constantPoint_self, inv_inv]
  exact h

/-- **The Weyl step.** Granting conjugacy of maximal tori, two torus-fixed lines `ρ(g₁) e_j`
and `ρ(g₂) e_j` in the orbit of the coordinate line `j`, whose stabilizer is the Borel subgroup
`B`, are related by a rational point `m` normalizing the torus: `m⁻¹ τ(s) m` is again a torus
point and `ρ(m g₂) e_j` is a multiple of `ρ(g₁) e_j`. -/
theorem exists_weyl_of_isTorusFixed (htorus : MaximalTorusConjugacyStatement.{u})
    [IsAffineHom G.X.hom] {B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G} (ht : IsMaximalTorus t)
    {b : B ⟶ G} (hb : IsBorelSubgroup b) (ρ : MatrixRepresentation G m) (j : m)
    (hstab : ∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
      x ∈ (SubgroupFunctor.range b).carrier Z ↔
        ∃ c : Γ(Z.left, ⊤)ˣ,
          (ρ.pointMatrix Z x : Matrix m m Γ(Z.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) : m → Γ(Z.left, ⊤)))
    {I : Type*} [Fintype I] (τ : (I → kˣ) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))
    (hτ : Set.range τ =
      Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.toGrp.X => z ≫ t.hom.hom)
    (g₁ g₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg₁ : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix (Pi.single j 1) g₁))
    (hg₂ : IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix (Pi.single j 1) g₂)) :
    ∃ n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, (∀ s, ∃ s', n⁻¹ * τ s * n = τ s') ∧
      ∃ c : k, orbitVec ρ.rationalMatrix (Pi.single j 1) (n * g₂) =
        c • orbitVec ρ.rationalMatrix (Pi.single j 1) g₁ := by
  have hle₁ := range_conj_le_of_isTorusFixed ht hb ρ j hstab τ hτ g₁ hg₁
  have hle₂ := range_conj_le_of_isTorusFixed ht hb ρ j hstab τ hτ g₂ hg₂
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsClosedImmersion t.hom.hom.left := ht.2.1
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  have hmono : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      Mono (t ≫ (G.innerIso g).hom).hom.hom := by
    intro g
    have : IsIso (G.innerIso g).hom.hom.hom :=
      (inferInstance : IsIso ((Grp.forget _).mapIso (G.innerIso g)).hom)
    change Mono (t.hom.hom ≫ (G.innerIso g).hom.hom.hom)
    infer_instance
  have := hmono g₁⁻¹
  have := hmono g₂⁻¹
  -- The two conjugated tori are maximal tori of `B`.
  let f₁ := SubgroupFunctor.factorOfRangeLE hle₁
  let f₂ := SubgroupFunctor.factorOfRangeLE hle₂
  have hf₁ : f₁ ≫ b = t ≫ (G.innerIso g₁⁻¹).hom := SubgroupFunctor.factorOfRangeLE_comp hle₁
  have hf₂ : f₂ ≫ b = t ≫ (G.innerIso g₂⁻¹).hom := SubgroupFunctor.factorOfRangeLE_comp hle₂
  have hf₁max : IsMaximalTorus f₁ :=
    IsMaximalTorus.of_comp hb.isClosedSubgroup (hf₁ ▸ ht.comp_iso (G.innerIso g₁⁻¹))
  have hf₂max : IsMaximalTorus f₂ :=
    IsMaximalTorus.of_comp hb.isClosedSubgroup (hf₂ ▸ ht.comp_iso (G.innerIso g₂⁻¹))
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  -- They are conjugate in `B`; hence `n = g₂ β g₁⁻¹` normalizes `t`.
  obtain ⟨β, φ, hβ⟩ := htorus k B T T f₁ f₂ hf₁max hf₂max
  have hn : t ≫ (G.innerIso (g₂ * (β ≫ b.hom.hom) * g₁⁻¹)).hom =
      CommGroupScheme.groupHom φ.hom ≫ t := by
    calc t ≫ (G.innerIso (g₂ * (β ≫ b.hom.hom) * g₁⁻¹)).hom
        = (t ≫ (G.innerIso g₁⁻¹).hom) ≫ (G.innerIso (β ≫ b.hom.hom)).hom ≫
            (G.innerIso g₂).hom := by
          rw [innerIso_mul_hom, innerIso_mul_hom, Category.assoc]
      _ = f₁ ≫ (B.innerIso β).hom ≫ b ≫ (G.innerIso g₂).hom := by
          rw [← hf₁, Category.assoc, ← Category.assoc b, comp_innerIso_hom_comp,
            Category.assoc]
      _ = CommGroupScheme.groupHom φ.hom ≫ (f₂ ≫ b) ≫ (G.innerIso g₂).hom := by
          rw [← Category.assoc f₁, hβ]
          simp only [Category.assoc]
      _ = CommGroupScheme.groupHom φ.hom ≫ t := by
          rw [hf₂, Category.assoc, ← innerIso_mul_hom, mul_inv_cancel, innerIso_one_hom,
            Category.comp_id]
  refine ⟨(g₂ * (β ≫ b.hom.hom) * g₁⁻¹)⁻¹, fun s => ?_, ?_⟩
  · obtain ⟨z, hz⟩ : τ s ∈ Set.range fun z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        T.toGrp.X => z ≫ t.hom.hom := by
      rw [← hτ]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ : (z ≫ (CommGroupScheme.groupHom φ.hom).hom.hom) ≫ t.hom.hom ∈
        Set.range τ := by
      rw [hτ]
      exact ⟨_, rfl⟩
    refine ⟨s', ?_⟩
    have h := congrArg (fun f : T.toGrp ⟶ G => z ≫ f.hom.hom) hn
    simp only [Grp.comp_hom_hom] at h
    rw [← Category.assoc, comp_innerIso_hom, constantPoint_self, ← Category.assoc] at h
    rw [hs', inv_inv, ← hz, h]
  · have hβ' : (β ≫ b.hom.hom)⁻¹ ∈
        (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
      inv_mem (SubgroupFunctor.mem_range.mpr ⟨β, rfl⟩)
    obtain ⟨c, hc⟩ := ((hstab _ _).trans (exists_unit_pointMatrix_iff ρ j _)).mp hβ'
    refine ⟨c, ?_⟩
    have hmul : (g₂ * (β ≫ b.hom.hom) * g₁⁻¹)⁻¹ * g₂ = g₁ * (β ≫ b.hom.hom)⁻¹ := by
      group
    rw [hmul]
    unfold orbitVec
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hc, mulVec_smul]

/-- **The covering core of the flag step, from its prerequisites.** Granting the existence of a
Borel subgroup with proper quotient, conjugacy of Borel subgroups, conjugacy of maximal tori,
finite Galois splitting of tori and the fixed-point theorem for smooth connected solvable
groups, the covering core `FlagCoreDualLineStatement` holds. -/
theorem flagCoreDualLine_of_prerequisites (hproper : SomeBorelQuotientProperStatement.{u})
    (hconj : BorelConjugacyStatement.{u}) (htorus : MaximalTorusConjugacyStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hfix : SolvableProperFixedPointStatement.{u}) : FlagCoreDualLineStatement.{u} := by
  intro k _ _ G _ _ _ T t ht U i hthrough B b hb n j ρ hstab hspan g
  have he : (Pi.single j 1 : Fin (n + 1) → k) ≠ 0 := fun h =>
    one_ne_zero (α := k) (by simpa using congrFun h j)
  obtain ⟨w₀, hw₀, hs₀⟩ := exists_stabilizesLine_dual hfix hb ρ
  have hse := stabilizesLine_single ρ j hstab
  -- Closed orbits, from a proper quotient by `B`.
  obtain ⟨Q, q, hQ, hsm, hsurj, hqc, hfib⟩ := exists_proper_quotient hproper hconj hb
  have ho₁ := isClosedOrbit_orbitVec q ρ he (fibersStabilizeLine_of_fibersInCosets hfib hse)
  have ho₂ := isClosedOrbit_dualOrbitVec q ρ hw₀ (fibersStabilizeLine_of_fibersInCosets hfib hs₀)
  have ho₃ := isClosedOrbit_tensorOrbitVec q ρ he hw₀
    (fibersStabilizeLine_of_fibersInCosets hfib (hse.tensor hs₀))
  -- The maximal torus acts diagonally.
  obtain ⟨I, _, P, wt, τ, hτ, hrange⟩ := exists_torusDiagonal hsplit ht ρ
  -- The stabilizer of the line `e_j` stabilizes the dual line `w₀`.
  have hstab' : ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (∃ c : k, orbitVec ρ.rationalMatrix (Pi.single j 1) h = c • Pi.single j 1) →
        ∃ c : k, w₀ ᵥ* (ρ.rationalMatrix h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = c • w₀ := by
    intro h hc
    have hh := ((hstab _ h).trans (exists_unit_pointMatrix_iff ρ j h)).mpr hc
    obtain ⟨c, hc'⟩ := hs₀.rational (inv_mem hh)
    refine ⟨c, ?_⟩
    rwa [rationalMatrix_dual, inv_inv, mulVec_transpose] at hc'
  have hU : ∀ g, IsTorusFixed ρ.rationalMatrix τ (orbitVec ρ.rationalMatrix (Pi.single j 1) g) →
      ∀ x ∈ rationalImage i, ∃ c : k,
        (ρ.rationalMatrix x : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
            orbitVec ρ.rationalMatrix (Pi.single j 1) g =
          c • orbitVec ρ.rationalMatrix (Pi.single j 1) g := by
    rintro g hg _ ⟨x, rfl⟩
    exact stable_of_isTorusFixed ht hb hthrough ρ j hstab τ hrange g hg x
  obtain ⟨w, hw, hwU⟩ := exists_semiInvariant_form ρ.rationalMatrix he hw₀ hspan hstab' ho₁ ho₂
    ho₃ P wt τ hτ (rationalImage i) hU
    (fun g₁ g₂ h₁ h₂ => exists_weyl_of_isTorusFixed htorus ht hb ρ j hstab τ hrange g₁ g₂ h₁ h₂) g
  exact ⟨w, hw, fun x => hwU _ ⟨x, rfl⟩⟩

end Langlands.GroupScheme.FlagCore
