# Adelic covariance for bounded extensions between form completions

`BoundedExtensionsIntertwine` says that every bounded linear extension of the
prescribed map on the original carriers intertwines the supplied adelic actions.
On the dense carriers, compatibility with the completed compact and finite
operators yields the corresponding intertwining identities. Joint-finite
Hilbert coefficient lifts and genuine enveloping covariance extend these
identities to the whole adelic group by analytic coefficient comparison.

`AdelicHilbertFormComparison` records a continuous linear equivalence of the
given completions that extends the original equivalence, scales the inner
product by a positive real ratio and intertwines the adelic actions.
The existing positive form comparison supplies the extension and the ratio.
The bounded-extension criterion proves full covariance for that extension.
These are internal consequences of completed-action compatibility, analytic
coefficient comparison and positive form comparison.

`AdelicCompletion` keeps an adelic action on the given form completion
together with the enveloping operators used in its joint-finite coefficient
lifts and both bounded-action comparisons. Its `formComparison` theorem
uses the comparisons for two such actions to prove full covariance of
the given extension.
