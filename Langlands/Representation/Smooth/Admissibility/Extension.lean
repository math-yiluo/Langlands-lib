import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Langlands.Representation.Filtration.ObjectDefinitions

/-! Admissibility of extensions and of finitely filtered representations. -/

namespace Langlands

universe uR uG uU uV uW

variable {R : Type uR} {G : Type uG} {U : Type uU} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Over a Noetherian ring, a smooth `σ` is admissible when an injective
intertwiner `i` from an admissible `ρ` and an intertwiner `q` to an admissible
`τ` satisfy the one-way inclusion `ker q ⊆ range i` (hypothesis `hexact`).
Neither `q ∘ i = 0` nor surjectivity of `q` is assumed. -/
theorem isAdmissible_of_extension [IsNoetherianRing R]
    {ρ : Representation R G U} {σ : Representation R G V} {τ : Representation R G W}
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (hexact : ∀ v, q v = 0 → ∃ u, i u = v)
    (hσ : IsSmooth σ) (hρ : IsAdmissible ρ) (hτ : IsAdmissible τ) : IsAdmissible σ := by
  refine ⟨hσ, fun K => ?_⟩
  have : Module.Finite R (fixedVectors ρ K.toSubgroup) := hρ.2 K
  have : Module.Finite R (fixedVectors τ K.toSubgroup) := hτ.2 K
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker (fixedVectorsMap q K.toSubgroup)
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    have hle : LinearMap.ker (fixedVectorsMap q K.toSubgroup) ≤
        LinearMap.range (fixedVectorsMap i K.toSubgroup) := by
      intro v hv
      obtain ⟨u, hu⟩ := hexact v (congrArg Subtype.val hv)
      refine ⟨⟨u, ?_⟩, Subtype.ext hu⟩
      change ∀ k : K.toSubgroup, ρ (k : G) u = u
      intro k
      apply hi
      rw [i.isIntertwining, hu]
      exact v.property k
    rw [← Submodule.map_comap_eq_of_le hle]
    exact (IsNoetherian.noetherian _).map _

/-- Every subrepresentation of a smooth representation is smooth. -/
theorem isSmooth_subrepresentation {ρ : Representation R G V} (hρ : IsSmooth ρ)
    (S : Subrepresentation ρ) : IsSmooth S.toRepresentation := by
  intro v
  obtain ⟨K, hK⟩ := hρ v
  exact ⟨K, fun k => Subtype.ext (hK k)⟩

/-- A smooth representation with a finite filtration by subrepresentations
whose graded quotients are all admissible is admissible, over a Noetherian ring. -/
theorem isAdmissible_of_objectRepFiltration [IsNoetherianRing R] {A : Rep.{uV} R G} {n : ℕ}
    (s : ObjectRepFiltration A n) (hA : IsSmooth A.ρ)
    (hgr : ∀ i, IsAdmissible (s.gradedRepresentation i).ρ) : IsAdmissible A.ρ := by
  have hstep : ∀ k (hk : k < n + 1),
      IsAdmissible (s.subrepresentation ⟨k, hk⟩).toRepresentation := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨isSmooth_subrepresentation hA _, fun K => ?_⟩
      have hbot : s.subrepresentation ⟨0, hk⟩ = ⊥ := s.subrepresentation_zero
      have : Subsingleton (s.subrepresentation ⟨0, hk⟩).toSubmodule := by
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        apply Subtype.ext
        change a = b
        rw [hbot] at ha hb
        rw [(Submodule.mem_bot R).1 ha, (Submodule.mem_bot R).1 hb]
      infer_instance
    | succ k ih =>
      intro hk
      let i : Fin n := ⟨k, by omega⟩
      have hlow := ih (by omega)
      let incl : (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
          (s.subrepresentation i.succ).toRepresentation :=
        { toLinearMap := Submodule.inclusion
            (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
          isIntertwining' := fun _ => rfl }
      exact isAdmissible_of_extension (ρ := (s.subrepresentation i.castSucc).toRepresentation)
        incl (s.gradedProjection i).hom
        (fun a b h => Subtype.ext
          (congrArg (fun x : (s.subrepresentation i.succ).toSubmodule => (x : A)) h))
        (by
          intro v hv
          have hmem := (Submodule.Quotient.mk_eq_zero _).1 hv
          exact ⟨⟨v, hmem⟩, rfl⟩)
        (isSmooth_subrepresentation hA _) hlow (hgr i)
  have htop := hstep n (Nat.lt_succ_self n)
  have hlast : s.subrepresentation ⟨n, Nat.lt_succ_self n⟩ = ⊤ := s.subrepresentation_last
  let f : A.ρ.IntertwiningMap (s.subrepresentation ⟨n, Nat.lt_succ_self n⟩).toRepresentation :=
    { toLinearMap :=
        { toFun := fun v => ⟨v, by rw [hlast]; trivial⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  exact isAdmissible_of_injective f (fun v w h => congrArg Subtype.val h) htop

end Langlands
