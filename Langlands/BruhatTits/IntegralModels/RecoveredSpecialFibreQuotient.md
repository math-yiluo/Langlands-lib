# Reductive quotients along an actual residue recovery isomorphism

This internal construction combines the published coefficient base change of special-fibre quotients with special-fibre isomorphism transport. It uses a supplied actual residue recovery isomorphism and asserts no recovery or quotient existence theorem.

Work in arbitrary universe `u`. Let `R → A` be a local homomorphism of local domains, with fraction fields `K → L` and compatible scalar towers through both `A` and `K`. Let `D` be relative-component model data over `R` in a group over `K`, and let `E` be relative-component model data over `A` in a possibly different group over `L`. Write `resExt` for the induced residue-field coefficient map. Supply `Q : SpecialFibreQuotientData D` and an actual isomorphism `e : BC_resExt D.neutral.specialFibre ≅ E.neutral.specialFibre`.

`Q.baseChangeSpecialFibreIso A L e` first uses `Q.baseChange A L`, then transports its ambient special fibre along `specialFibreSquareIso.symm ≪≫ e`. This permits use of the exact supplied `e` without identifying it with a separately implemented coefficient-square isomorphism. The quotient is definitionally `BC_resExt Q.quotient`. Its projection simplifies to `e.inv ≫ BC_resExt Q.projection`.

`isReductiveQuotient_baseChangeSpecialFibreIso` additionally assumes that the induced residue-field extension is separable and algebraic and that `Q.IsReductiveQuotient`. The published coefficient-base-change theorem preserves the unipotent radical, fppf quotient and connected reductivity, and special-fibre isomorphism transport preserves that full predicate again.

`baseChangeSpecialFibreIso_hom_projection`, with its reassociated version, proves the exact equation `e.hom ≫ recovered.projection = BC_resExt Q.projection` by isomorphism cancellation. `baseChangeSpecialFibreIso_torus_projection` applies it to any supplied residue group maps `t`, `t'` and `s` with `s ≫ t' = BC_resExt t ≫ e.hom`; its conclusion is `s ≫ t' ≫ recovered.projection = BC_resExt (t ≫ Q.projection)`. The commutative source group schemes need not themselves satisfy a torus predicate.

For unramified local-field applications the published residue algebraicity and separability results provide the extension hypotheses. The actual neutral recovery isomorphism, lower and upper torus maximality, root survival, root restriction nonvanishing and chamber construction remain separate inputs or obligations.
