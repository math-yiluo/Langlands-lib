import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.TwistedCharacterRegularValuesReduction

/-!
# Unramified twists, induced σ-intertwiners and the conditions of the twisted trace
Paley–Wiener theorem

Generic part, for a topological group `G` with an automorphism `θ`: unramified characters
(trivial on every compact subgroup), the θ-intertwiner of an unramified twist, the
θ-intertwiner `(ι B f)(g) = B (f (θ⁻¹ g))` of a smoothly induced representation
(Rogawski 1988, §3; Henniart–Lemaire 2011, II.4.4), and, for a linear functional `Φ` on the
distributions on `G`, the compact-domination condition (Henniart–Lemaire 2011, II.5.7,
Remarque (1), condition (i)') and the trace-functional condition (II.5.7, condition (B)).

`GL_n` part, in namespace `TwistedPaleyWiener` to keep these names apart from the Library's
normalized versions: continuity of the inverse entrywise action of `σ` and the σ-intertwiner
of the unnormalized smooth induction from a standard block parabolic subgroup. Finally, the
regularity condition on induced families (Henniart–Lemaire 2011, II.5.7, condition (A)(ii);
Rogawski 1988, §11, condition (II)). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uG uM uV uX u v z

/-! ## Unramified characters and twists -/

section Unramified

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- `ψ` is unramified: it is trivial on every compact subgroup of `G`. For the Levi
subgroups `∏ᵢ GL_{nᵢ}(E)` of `GL_n(E)` over a nonarchimedean local field these are exactly
the characters `m ↦ ∏ᵢ zᵢ ^ ord(det mᵢ)` with `zᵢ ∈ ℂˣ` (see the paired Markdown). -/
def IsUnramifiedCharacter (ψ : G →* ℂˣ) : Prop :=
  ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, ψ k = 1

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] in
/-- If `ψ ∘ θ = ψ`, a θ-intertwiner `A` of `ρ` is also a θ-intertwiner of the twist
`ρ ⊗ ψ` (same linear map). -/
def twistTwistedIntertwiner (θ : G ≃* G) (ψ : G →* ℂˣ) (hψ : ∀ g, ψ (θ g) = ψ g)
    {ρ : Representation ℂ G V} (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (twist ψ ρ).Equiv ((twist ψ ρ).comp θ.toMonoidHom) where
  toLinearEquiv := A.toLinearEquiv
  isIntertwining' g := by
    ext v
    change A ((ψ g : ℂ) • ρ g v) = (ψ (θ g) : ℂ) • ρ (θ g) (A v)
    rw [map_smul, hψ g]
    congr 1
    exact Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap g v

omit [TopologicalSpace G] in
@[simp]
theorem twistTwistedIntertwiner_apply (θ : G ≃* G) (ψ : G →* ℂˣ) (hψ : ∀ g, ψ (θ g) = ψ g)
    {ρ : Representation ℂ G V} (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) (v : V) :
    twistTwistedIntertwiner θ ψ hψ A v = A v :=
  rfl

end Unramified

/-! ## The θ-intertwiner of a smoothly induced representation -/

section Induced

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type uM} [Group M]
variable {X : Type uX} [AddCommGroup X] [Module ℂ X]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The restriction of `θ` to a subgroup `P` with `θ g ∈ P ↔ g ∈ P`. -/
private def stableSubgroupAut (θ : G ≃* G) (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P) :
    P ≃* P :=
  (θ.subgroupMap P).trans (MulEquiv.subgroupCongr (show P.map θ.toMonoidHom = P by
    ext g
    rw [Subgroup.mem_map_equiv, ← hP (θ.symm g), MulEquiv.apply_symm_apply]))

/-- The θ-intertwiner `(ι B f)(g) = B (f (θ⁻¹ g))` of the smooth induction `Ind_P^G (Ξ ∘ p)`,
for a θ-stable subgroup `P`, a homomorphism `p : P → M` with `p ∘ θ = θ_M ∘ p`, and a
`θ_M`-intertwiner `B : Ξ ≅ Ξ ∘ θ_M` (Rogawski 1988, §3; Henniart–Lemaire 2011, II.4.4). It is
the Library's transport `Induction.transportSmoothEquiv` along `θ` and its restriction to `P`,
with `T = B`; its inverse is `f ↦ (g ↦ B⁻¹ (f (θ g)))`. -/
def inducedTwistedIntertwiner (θ : G ≃* G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M) (θM : M ≃* M)
    (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x)) (Ξ : Representation ℂ M X)
    (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom)) :
    (Induction.smoothInduced P (Ξ.comp p)).Equiv
      ((Induction.smoothInduced P (Ξ.comp p)).comp θ.toMonoidHom) :=
  Induction.transportSmoothEquiv P θ hθ hθ' (stableSubgroupAut θ P hP) (fun _ => rfl)
    B.toLinearEquiv (by
      intro q x
      change B (Ξ (p q) x) = Ξ (p ⟨θ q, (hP q).2 q.2⟩) (B x)
      rw [hp q]
      exact Representation.IntertwiningMap.isIntertwining _ _ B.toIntertwiningMap (p q) x)

theorem eval_inducedTwistedIntertwiner (θ : G ≃* G) (hθ : Continuous θ)
    (hθ' : Continuous θ.symm) (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M)
    (θM : M ≃* M) (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x)) (Ξ : Representation ℂ M X)
    (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom)) (f : Induction.SmoothFunctions P (Ξ.comp p))
    (g : G) :
    Induction.eval P (Ξ.comp p) (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B f) g =
      B (Induction.eval P (Ξ.comp p) f (θ.symm g)) :=
  rfl

end Induced

/-! ## Conditions on linear functionals on distributions -/

section Conditions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  (θ : G ≃* G) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

/-- Condition (i)' of the twisted trace Paley–Wiener theorem (Henniart–Lemaire 2011, II.5.7,
Remarque (1); Bernstein–Deligne–Kazhdan 1986, §1.2, condition (ii)), at carrier universe `z`:
there is a compact open subgroup `J` of `G` such that `Φ(Θ^A_π) = 0` for every irreducible
admissible `π` without nonzero `J`-fixed vectors and every `A : π ≅ π ∘ θ`. -/
def IsCompactlyDominatedFunctional (Φ : Module.Dual ℂ (Distribution G)) : Prop :=
  ∃ J : OpenSubgroup G, IsCompact (J : Set G) ∧
    ∀ (V : Type z) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
      (hπ : IsAdmissible π), π.IsIrreducible → fixedVectors π J.toSubgroup = ⊥ →
        ∀ A : π.Equiv (π.comp θ.toMonoidHom),
          Φ (twistedDistribution μ π hπ A.toLinearMap) = 0

/-- Condition (B) of the twisted trace Paley–Wiener theorem (Henniart–Lemaire 2011, II.5.7),
at carrier universe `z`: there is `φ ∈ C^∞_c(G)` with `Θ^A_π(φ) = Φ(Θ^A_π)` for every
irreducible admissible `π` and every `A : π ≅ π ∘ θ`. -/
def IsTwistedTraceFunctional (Φ : Module.Dual ℂ (Distribution G)) : Prop :=
  ∃ φ : SchwartzBruhat G,
    ∀ (V : Type z) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
      (hπ : IsAdmissible π), π.IsIrreducible → ∀ A : π.Equiv (π.comp θ.toMonoidHom),
        twistedDistribution μ π hπ A.toLinearMap φ =
          Φ (twistedDistribution μ π hπ A.toLinearMap)

end Conditions

/-! ## `GL_n`: the induced σ-intertwiner and the regularity condition -/

section GeneralLinearGroup

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]

namespace TwistedPaleyWiener

omit [IsTopologicalRing E] in
/-- The inverse entrywise action is continuous by the module-topology continuity theorem
applied to the inverse algebra automorphism. Unlike the Library's
`Langlands.BaseChange.continuous_entrywiseAut_symm`, `F` is only a commutative ring. -/
theorem continuous_entrywiseAut_symm (σ : E ≃ₐ[F] E) (n : ℕ) :
    Continuous (entrywiseAut σ n).symm :=
  continuous_entrywiseAut_of_isModuleTopology σ.symm n

/-- The σ-intertwiner `(ι B f)(g) = B (f (σ⁻¹(g)))` of the unnormalized smooth induction
`Ind_P^G (Ξ ∘ p)` from the standard block parabolic `P` of `B`, for a σ-intertwiner
`BΞ : Ξ ≅ Ξ^σ` of a representation `Ξ` of the Levi product (Henniart–Lemaire 2011, II.4.4,
the map `ι_α`; Rogawski 1988, §3). -/
def inducedSigmaIntertwiner (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) {X : Type uX}
    [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom)) :
    SigmaIntertwiner σ n
      (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E))) :=
  inducedTwistedIntertwiner (entrywiseAut σ n) (continuous_entrywiseAut_of_isModuleTopology σ n)
    (TwistedPaleyWiener.continuous_entrywiseAut_symm σ n) (B.parabolic E)
    (entrywiseAut_mem_parabolic_iff σ B) (B.leviProjection E) (leviAut σ B)
    (leviProjection_entrywiseAut σ B) Ξ BΞ

theorem eval_inducedSigmaIntertwiner (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    {X : Type uX} [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (B.Levi E) X)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom))
    (f : Induction.SmoothFunctions (B.parabolic E) (Ξ.comp (B.leviProjection E)))
    (g : GeneralLinear n E) :
    Induction.eval _ _ (TwistedPaleyWiener.inducedSigmaIntertwiner σ B Ξ BΞ f) g =
      BΞ (Induction.eval _ _ f ((entrywiseAut σ n).symm g)) :=
  rfl

end TwistedPaleyWiener

variable {n : ℕ} [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]

/-- Condition (A)(ii) of the twisted trace Paley–Wiener theorem for `GL_n(E)`
(Henniart–Lemaire 2011, II.5.7; Rogawski 1988, §11, condition (II)), at carrier universe
`z`: for every block shape `B` of `n`, every irreducible admissible representation `Ξ` of the
Levi product `∏ᵢ GL_{nᵢ}(E)` and every σ-intertwiner `BΞ : Ξ ≅ Ξ^σ`, the function
`ψ ↦ Φ(Θ^{ι(BΞ)}_{Ind(Ξ ⊗ ψ)})` on the σ-invariant unramified characters `ψ` of the Levi
product is regular, that is, a finite linear combination `∑_{m ∈ s} c(m) ψ(m)` of
evaluations at elements of the Levi product. The induction is the Library's unnormalized
smooth induction from the standard block parabolic subgroup, and `ι(BΞ)` is
`TwistedPaleyWiener.inducedSigmaIntertwiner` (not the Library's normalized
`Langlands.BaseChange.inducedSigmaIntertwiner`). -/
def IsSigmaInducedRegularFunctional (σ : E ≃ₐ[F] E) (μ : Measure (GeneralLinear n E))
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (Φ : Module.Dual ℂ (Distribution (GeneralLinear n E))) : Prop :=
  ∀ (B : BlockShape n) (X : Type z) [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X), IsAdmissible Ξ → Ξ.IsIrreducible →
    ∀ BΞ : Ξ.Equiv (Ξ.comp (leviAut σ B).toMonoidHom),
      ∃ (s : Finset (B.Levi E)) (c : B.Levi E → ℂ),
        ∀ (ψ : B.Levi E →* ℂˣ), IsUnramifiedCharacter ψ →
          ∀ (hψ : ∀ m, ψ (leviAut σ B m) = ψ m)
            (h : IsAdmissible (Induction.smoothInduced (B.parabolic E)
              ((twist ψ Ξ).comp (B.leviProjection E)))),
            Φ (twistedDistribution μ _ h
              (TwistedPaleyWiener.inducedSigmaIntertwiner σ B (twist ψ Ξ)
                (twistTwistedIntertwiner (leviAut σ B) ψ hψ BΞ)).toLinearMap) =
              ∑ m ∈ s, c m * (ψ m : ℂ)

end GeneralLinearGroup

end Langlands.BaseChange
